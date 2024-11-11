import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Vector.Defs

open Mathlib

abbrev ZVector (dim : ℕ) := Vector ℤ dim

/- Define element-wise addition and subtraction of lists of integers -/
/- If the lists have different lengths, returns the empty list -/
private def ZList.add (x y : List ℤ) : List ℤ :=
  if x.length = y.length then
    List.map (fun (pair : ℤ × ℤ) => pair.fst + pair.snd) (List.zip x y)
  else List.nil
private instance : Add (List ℤ) where
  add := ZList.add

private def ZList.sub (x y : List ℤ) : List ℤ :=
  if x.length = y.length then
    List.map (fun (pair : ℤ × ℤ) => pair.fst - pair.snd) (List.zip x y)
  else List.nil
private instance : Sub (List ℤ) where
  sub := ZList.sub

private theorem ZList.same_lengths_add_assoc :
    ∀ (u v w : List ℤ) (_ : u.length = v.length) (_ : v.length = w.length),
    add (add u v) w = add u (add v w) := by
  intro _ _ _ h₁ h₂; unfold add; rw [h₁, h₂]; simp; rw [h₁, h₂]; simp
  rw [List.zip_map_left, List.zip_map_right, List.map_map, List.map_map]; unfold Function.comp; simp; apply List.ext_getElem
  . simp
  . simp; intros; exact Int.add_assoc _ _ _

/- Define addition and subtraction of vectors of integers with the same length -/
def ZVector.add {dim : ℕ} (x y : Vector ℤ dim) : Vector ℤ dim :=
  ⟨ZList.add x.toList y.toList, by rw [ZList.add]; simp⟩
instance {dim : ℕ} : Add (Vector ℤ dim) where
  add := ZVector.add

def ZVector.sub {dim : ℕ} (x y : Vector ℤ dim) : Vector ℤ dim :=
  ⟨ZList.sub x.toList y.toList, by rw [ZList.sub]; simp⟩
instance {dim : ℕ} : Sub (Vector ℤ dim) where
  sub := ZVector.sub

/- Define zero vector -/
def ZVector.zero (dim : ℕ) : Vector ℤ dim := Vector.replicate dim 0
instance {dim : ℕ} : Zero (Vector ℤ dim) where
  zero := ZVector.zero dim

/- Define negation of vector -/
def ZVector.neg {dim : ℕ} (x : Vector ℤ dim) : Vector ℤ dim := sub (zero dim) x
instance {dim : ℕ} : Neg (Vector ℤ dim) where
  neg := ZVector.neg

/- Define scalar multiplication of vectors of integers by naturals and integers -/
def ZVector.nsmul {dim : ℕ} (n : ℕ) (x : Vector ℤ dim) : Vector ℤ dim :=
  if n = 0 then zero dim else add (nsmul (n - 1) x) x
instance {dim : ℕ} : SMul ℕ (Vector ℤ dim) where
  smul := ZVector.nsmul

def ZVector.zsmul {dim : ℕ} (n : ℤ) (x : Vector ℤ dim) : Vector ℤ dim :=
  if n < 0 then neg (nsmul (Int.toNat (-n)) x) else nsmul (Int.toNat n) x
instance {dim : ℕ} : SMul ℤ (Vector ℤ dim) where
  smul := ZVector.zsmul

/- Miscellaneous theorems -/
theorem ZVector.add_comm {dim : ℕ} : ∀ (u v : Vector ℤ dim), add u v = add v u := by
  intros; unfold add; apply Vector.eq; unfold ZList.add; simp; apply List.ext_getElem
  . simp
  . simp; intros; exact Int.add_comm _ _

theorem ZVector.add_assoc {dim : ℕ} : ∀ (u v w : Vector ℤ dim), add (add u v) w = add u (add v w) := by
  intros; unfold add; apply Vector.eq; simp;
  apply ZList.same_lengths_add_assoc _ _ _; simp; simp;

theorem ZVector.zero_add {dim : ℕ} : ∀ (x : Vector ℤ dim), add (zero dim) x = x := by
  intro; unfold zero; unfold Vector.replicate; apply Vector.eq; apply List.ext_getElem
  . simp
  . simp; intros; unfold add; unfold ZList.add; simp;

theorem ZVector.add_zero {dim : ℕ} : ∀ (x : Vector ℤ dim), add x (zero dim) = x := by
  intro; rw [add_comm]; exact zero_add _

theorem ZVector.neg_add_cancel {dim : ℕ} : ∀ (x : Vector ℤ dim), add (neg x) x = zero dim := by
  intro; unfold neg; unfold zero; unfold Vector.replicate; apply Vector.eq; apply List.ext_getElem
  . simp
  . simp; intros; unfold sub; unfold add; unfold ZList.sub; unfold ZList.add; simp; exact Int.add_left_neg _

theorem ZVector.sub_eq_add_neg {dim : ℕ} : ∀ (u v : Vector ℤ dim), sub u v = add u (neg v) := by
  intros; unfold neg; unfold zero; unfold Vector.replicate; apply Vector.eq; apply List.ext_getElem
  . simp
  . simp; intros; unfold sub; unfold add; unfold ZList.sub; unfold ZList.add; simp; rfl

theorem ZVector.nsmul_zero {dim : ℕ} : ∀ (x : Vector ℤ dim), nsmul 0 x = zero dim := by
  unfold nsmul; simp;

theorem ZVector.nsmul_succ {dim : ℕ} : ∀ (n : ℕ) (x : Vector ℤ dim),
    nsmul (Nat.succ n) x = add (nsmul n x) x := by
  intros; rw [nsmul]; simp

theorem ZVector.zsmul_zero' {dim : ℕ} : ∀ (x : Vector ℤ dim), zsmul 0 x = zero dim := by
  exact nsmul_zero

theorem ZVector.zsmul_succ' {dim : ℕ} : ∀ (n : ℕ) (x : Vector ℤ dim),
    zsmul (Nat.succ n) x = add (zsmul n x) x := by
  exact nsmul_succ

theorem ZVector.zsmul_neg' {dim : ℕ} : ∀ (n : ℕ) (x : Vector ℤ dim),
    zsmul (Int.negSucc n) x = neg (zsmul (Int.ofNat (Nat.succ n)) x) := by
  intros; unfold zsmul; simp_rw [Int.negSucc_lt_zero, ite_true]; rfl

/- Vectors of integers form an additive commutative group under addition -/
instance ZVector.addCommGroup {dim : ℕ} : AddCommGroup (Vector ℤ dim) where
  add := add
  add_assoc := add_assoc
  zero := zero dim
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmul
  nsmul_zero := nsmul_zero
  nsmul_succ := nsmul_succ
  neg := neg
  sub := sub
  sub_eq_add_neg := sub_eq_add_neg
  zsmul := zsmul
  zsmul_zero' := zsmul_zero'
  zsmul_succ' := zsmul_succ'
  zsmul_neg' := zsmul_neg'
  neg_add_cancel := neg_add_cancel
  add_comm := add_comm

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P14.e6_root_blocks
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:14:35.133367+00:00
-- url     : https://prove2.me/submissions/7cb0001d-8702-42df-a76f-36dcafdeb7c4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P14
namespace G64I
open scoped BigOperators
abbrev W := Fin 8 → ℚ
def kq (i : Fin 8) : W := fun j => if j = i then 1 else 0
def ftsQ : W := kq 0 + kq 1 + kq 2
def projQ (x : W) : W := fun j => if j.val < 3 then x j - (x 0 + x 1 + x 2) / 3 else 0
def ewQ (i : Fin 3) : W := (1 / 3 : ℚ) • (ftsQ - (3 : ℚ) • kq ⟨i.val, by omega⟩)
def cycQ (c : Fin 3) (x : W) : W := fun j =>
  if j.val < 3 then x ⟨(j.val + 3 - c.val) % 3, by omega⟩ else x j
def signQ (b : Bool) : ℚ := if b then 1 else -1
def plusCountQ {m : ℕ} (r : ℕ) (s : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun i => i.val < r ∧ s i = true).card
def halfSumsQ {m : ℕ} (a : Fin m → W) (p : (Fin m → Bool) → Prop) [DecidablePred p] : Finset W :=
  (Finset.univ.filter p).image fun s => (1 / 2 : ℚ) • ∑ i, signQ (s i) • a i
def signedQ (S : Finset W) : Finset W := S ∪ S.image (fun x => -x)
def differencesQ (I : Finset (Fin 8)) : Finset W :=
  I.biUnion fun i => (I.erase i).image fun j => kq i - kq j
def dRootsQ (I : Finset (Fin 8)) : Finset W :=
  I.biUnion fun i => (I.erase i).biUnion fun j =>
    {kq i + kq j, kq i - kq j, -kq i + kq j, -kq i - kq j}
def externalQ : Finset W := differencesQ {0, 1, 2}
def rootsG2Q : Finset W := externalQ ∪ signedQ (Finset.univ.image ewQ)
def rootsF4Q : Finset W :=
  signedQ (({0, 1, 2, 3} : Finset (Fin 8)).image kq) ∪ dRootsQ {0, 1, 2, 3} ∪
    halfSumsQ ![kq 0, kq 1, kq 2, kq 3] (fun _ => True)
def rootsE6Q : Finset W := dRootsQ {0, 1, 2, 3, 4} ∪
  halfSumsQ ![kq 0, kq 1, kq 2, kq 3, kq 4, kq 5] (fun s => plusCountQ 6 s % 2 = 1)
def rootsE7Q : Finset W :=
  signedQ {kq 6} ∪ dRootsQ {0, 1, 2, 3, 4, 5} ∪
    halfSumsQ ![kq 0, kq 1, kq 2, kq 3, kq 4, kq 5, kq 6] (fun s => plusCountQ 6 s % 2 = 0)
def rootsE8Q : Finset W := dRootsQ Finset.univ ∪ halfSumsQ kq (fun s => plusCountQ 8 s % 2 = 0)
def block1Q : Finset W :=
  {-kq 0, -kq 0 + kq 3, -kq 0 - kq 3,
   (1 / 2 : ℚ) • (-kq 0 + kq 1 + kq 2 + kq 3),
   (1 / 2 : ℚ) • (-kq 0 + kq 1 + kq 2 - kq 3), kq 1 + kq 2}
def center1Q : Finset W := signedQ
  {kq 3, (1 / 2 : ℚ) • (ftsQ + kq 3), (1 / 2 : ℚ) • (ftsQ - kq 3)}
def block2Q : Finset W :=
  {-kq 0 + kq 3, -kq 0 - kq 3, -kq 0 + kq 4, -kq 0 - kq 4, kq 1 + kq 2,
   (1 / 2 : ℚ) • (-kq 0 + kq 1 + kq 2 + kq 3 - kq 4 - kq 5),
   (1 / 2 : ℚ) • (-kq 0 + kq 1 + kq 2 + kq 3 + kq 4 + kq 5),
   (1 / 2 : ℚ) • (-kq 0 + kq 1 + kq 2 - kq 3 + kq 4 - kq 5),
   (1 / 2 : ℚ) • (-kq 0 + kq 1 + kq 2 - kq 3 - kq 4 + kq 5)}
def center2FirstQ : Finset W := signedQ
  {kq 3 + kq 4, (1 / 2 : ℚ) • (ftsQ - kq 3 - kq 4 - kq 5),
   (1 / 2 : ℚ) • (ftsQ + kq 3 + kq 4 - kq 5)}
def center2SecondQ : Finset W := signedQ
  {kq 3 - kq 4, (1 / 2 : ℚ) • (ftsQ - kq 3 + kq 4 + kq 5),
   (1 / 2 : ℚ) • (ftsQ + kq 3 - kq 4 + kq 5)}
def center2Q : Finset W := center2FirstQ ∪ center2SecondQ
def block4Q : Finset W :=
  {kq 1 + kq 2} ∪
  (({3, 4, 5} : Finset (Fin 8)).biUnion fun j => {-kq 0 + kq j, -kq 0 - kq j}) ∪
  ((Finset.univ.filter fun s : Fin 3 → Bool => plusCountQ 3 s % 2 = 0).biUnion
    fun s => Finset.univ.image fun b : Bool => (1 / 2 : ℚ) •
      (-kq 0 + kq 1 + kq 2 + (∑ i : Fin 3, signQ (s i) • kq ⟨i.val + 3, by omega⟩)
        + signQ b • kq 6))
def center4Q : Finset W := dRootsQ {3, 4, 5} ∪ signedQ {kq 6} ∪
  signedQ ((Finset.univ.filter fun s : Fin 3 → Bool => plusCountQ 3 s % 2 = 1).biUnion
    fun s => Finset.univ.image fun b : Bool => (1 / 2 : ℚ) •
      (ftsQ + (∑ i : Fin 3, signQ (s i) • kq ⟨i.val + 3, by omega⟩)
        + signQ b • kq 6))
def block8Q : Finset W := {kq 1 + kq 2} ∪
  (({3, 4, 5, 6, 7} : Finset (Fin 8)).biUnion fun j => {-kq 0 + kq j, -kq 0 - kq j}) ∪
  ((Finset.univ.filter fun s : Fin 5 → Bool => plusCountQ 5 s % 2 = 0).image
    fun s => (1 / 2 : ℚ) • (-kq 0 + kq 1 + kq 2 +
      ∑ i : Fin 5, signQ (s i) • kq ⟨i.val + 3, by omega⟩))
def center8Q : Finset W := dRootsQ {3, 4, 5, 6, 7} ∪
  signedQ ((Finset.univ.filter fun s : Fin 5 → Bool => plusCountQ 5 s % 2 = 1).image
    fun s => (1 / 2 : ℚ) • (ftsQ +
      ∑ i : Fin 5, signQ (s i) • kq ⟨i.val + 3, by omega⟩))
def orientedBlockQ (B : Finset W) (c : Fin 3) (positive : Bool) : Finset W :=
  if positive then B.image (cycQ c) else (B.image (cycQ c)).image (fun x => -x)
def pieceQ (C B : Finset W) : Bool ⊕ (Fin 3 × Bool) → Finset W
  | .inl false => externalQ
  | .inl true => C
  | .inr (c, b) => orientedBlockQ B c b
def rootPartitionQ (R C B : Finset W) (centralSize blockSize : ℕ) : Prop :=
  R = Finset.univ.biUnion (pieceQ C B) ∧
  (∀ i j : Bool ⊕ (Fin 3 × Bool), i ≠ j → Disjoint (pieceQ C B i) (pieceQ C B j)) ∧
  R.card = 6 + centralSize + 6 * blockSize ∧ externalQ.card = 6 ∧
  C.card = centralSize ∧
  (∀ c b, (orientedBlockQ B c b).card = blockSize) ∧
  (∀ x ∈ C, projQ x = 0) ∧ (∀ x ∈ externalQ, projQ x = x) ∧
  (∀ c b, ∀ x ∈ orientedBlockQ B c b,
    projQ x = if b then ewQ c else -ewQ c)
instance (R C B : Finset W) (a b : ℕ) : Decidable (rootPartitionQ R C B a b) := by
  unfold rootPartitionQ; infer_instance
def wdot (w : W) (p q : W) : ℚ := ∑ j, w j * (p j * q j)
def isA2Q (w : W) (R : Finset W) (a b : W) (l : ℚ) : Prop :=
  R = signedQ {a, b, a + b} ∧ wdot w a a = l ∧ wdot w b b = l ∧ wdot w a b = -l / 2
instance (w : W) (R : Finset W) (a b : W) (l : ℚ) : Decidable (isA2Q w R a b l) := by
  unfold isA2Q; infer_instance
def w1 : W := fun _ => 1
def w6 : W := fun j => if j = 5 then 3 else 1
def w7 : W := fun j => if j = 6 then 2 else 1
def d6Q : Fin 6 → W :=
  ![(1 / 2 : ℚ) • (-kq 0 - kq 3 - kq 4 - kq 5),
    (1 / 2 : ℚ) • (-kq 0 - kq 3 + kq 4 + kq 5),
    (1 / 2 : ℚ) • (-kq 0 + kq 3 - kq 4 + kq 5),
    (1 / 2 : ℚ) • (-kq 0 + kq 3 + kq 4 - kq 5),
    (1 / 2 : ℚ) • (kq 1 + kq 2 + kq 6),
    (1 / 2 : ℚ) • (kq 1 + kq 2 - kq 6)]
def etaDiffQ : Finset W := Finset.univ.biUnion fun i : Fin 6 =>
  (Finset.univ.erase i).image fun j => d6Q i - d6Q j
def etaSumsQ : Finset W := Finset.univ.biUnion fun i : Fin 6 =>
  (Finset.univ.filter fun j : Fin 6 => i < j).image fun j => d6Q i + d6Q j
def etaD6Q : Finset W := Finset.univ.biUnion fun i : Fin 6 =>
  (Finset.univ.filter fun j : Fin 6 => i < j).biUnion fun j =>
    {d6Q i + d6Q j, d6Q i - d6Q j, -d6Q i + d6Q j, -d6Q i - d6Q j}
def rebE6Q (x : W) : W :=
  (∑ i : Fin 5, x ⟨i.val, by omega⟩ • kq ⟨i.val + 3, by omega⟩) - (x 5) • ftsQ
def rebE7Q (x : W) : W :=
  (∑ i : Fin 5, x ⟨i.val, by omega⟩ • kq ⟨i.val + 3, by omega⟩) + x 5 • kq 0 + x 6 • (kq 1 + kq 2)
def zInnerQ : W := kq 3 + kq 4 + kq 5
def innerBlockQ (f : Fin 3) : Finset W :=
  let a := kq ⟨f.val + 3, by omega⟩
  {-a + kq 6, -a - kq 6, -a + kq 7, -a - kq 7, zInnerQ - a} ∪
  ((Finset.univ.image fun s : Fin 3 → Bool =>
    -a + (1 / 2 : ℚ) • (signQ (s 0) • ftsQ + zInnerQ +
      signQ (s 1) • kq 6 + signQ (s 2) • kq 7)).filter fun x => x ∈ rootsE8Q)
def nestedA2Q : Fin 4 → Finset W :=
  ![externalQ, differencesQ {3, 4, 5},
    signedQ {kq 6 + kq 7, (1 / 2 : ℚ) • (ftsQ + zInnerQ - kq 6 - kq 7),
      (1 / 2 : ℚ) • (ftsQ + zInnerQ + kq 6 + kq 7)},
    signedQ {kq 6 - kq 7, (1 / 2 : ℚ) • (-ftsQ + zInnerQ - kq 6 + kq 7),
      (1 / 2 : ℚ) • (-ftsQ + zInnerQ + kq 6 - kq 7)}]
def nestedPieceQ : Fin 4 ⊕ ((Fin 3 ⊕ Fin 3) × Bool) → Finset W
  | .inl i => nestedA2Q i
  | .inr (.inl c, b) => orientedBlockQ block8Q c b
  | .inr (.inr f, true) => innerBlockQ f
  | .inr (.inr f, false) => (innerBlockQ f).image (fun x => -x)
end G64I
namespace G64I
set_option maxRecDepth 100000 in
theorem qE6 : rootPartitionQ rootsE6Q center2Q block2Q 12 9 ∧
  isA2Q w6 center2FirstQ (kq 3 + kq 4) ((1 / 2 : ℚ) • (ftsQ - kq 3 - kq 4 - kq 5)) 2 ∧
  isA2Q w6 center2SecondQ (kq 3 - kq 4) ((1 / 2 : ℚ) • (ftsQ - kq 3 + kq 4 + kq 5)) 2 ∧
  (∀ x ∈ center2FirstQ, ∀ y ∈ center2SecondQ, wdot w6 x y = 0) := by decide +kernel
end G64I
noncomputable section

open QAlgorithms.Papers.Independent.Renew46.P14

open scoped BigOperators

local instance : DecidableEq V := Classical.decEq V

attribute [local instance] Classical.propDecidable

namespace G64I
open QAlgorithms.Papers.Independent.Renew46.P14

def Lc (c : Fin 8 → ℝ) (q : W) : V := fun j => (q j : ℝ) * c j

lemma Lc_add (c : Fin 8 → ℝ) (p q : W) : Lc c (p + q) = Lc c p + Lc c q := by
  ext j; simp [Lc]; ring
lemma Lc_neg (c : Fin 8 → ℝ) (p : W) : Lc c (-p) = -Lc c p := by
  ext j; simp [Lc]
lemma Lc_sub (c : Fin 8 → ℝ) (p q : W) : Lc c (p - q) = Lc c p - Lc c q := by
  ext j; simp [Lc]; ring
lemma Lc_smul (c : Fin 8 → ℝ) (a : ℚ) (p : W) : Lc c (a • p) = (a : ℝ) • Lc c p := by
  ext j; simp [Lc]; ring
lemma Lc_zero (c : Fin 8 → ℝ) : Lc c 0 = 0 := by ext j; simp [Lc]
def LcH (c : Fin 8 → ℝ) : W →+ V where
  toFun := Lc c
  map_zero' := Lc_zero c
  map_add' := Lc_add c
lemma Lc_sum (c : Fin 8 → ℝ) {ι : Type*} (s : Finset ι) (f : ι → W) :
    Lc c (∑ i ∈ s, f i) = ∑ i ∈ s, Lc c (f i) := map_sum (LcH c) f s
lemma Lc_kq (c : Fin 8 → ℝ) (i : Fin 8) : Lc c (kq i) = c i • k i := by
  ext j; simp only [Lc, kq, k, Pi.smul_apply, smul_eq_mul]
  split_ifs with h <;> simp [h]
lemma Lc_inj (c : Fin 8 → ℝ) (hc : ∀ j, c j ≠ 0) : Function.Injective (Lc c) := by
  intro p q h; ext j
  have := congrFun h j
  simp only [Lc] at this
  exact_mod_cast mul_right_cancel₀ (hc j) this
lemma signQ_cast (b : Bool) : ((signQ b : ℚ) : ℝ) = sign b := by
  cases b <;> simp [signQ, sign]
lemma plusCount_eq {m : ℕ} (r : ℕ) (s : Fin m → Bool) : plusCount r s = plusCountQ r s := by
  unfold plusCount plusCountQ
  exact congrArg Finset.card (Finset.ext fun i => by simp only [Finset.mem_filter])

def c1 : Fin 8 → ℝ := fun _ => 1
def c6 : Fin 8 → ℝ := fun j => if j = 5 then Real.sqrt 3 else 1
def c7 : Fin 8 → ℝ := fun j => if j = 6 then Real.sqrt 2 else 1
lemma c1_ne (j : Fin 8) : c1 j ≠ 0 := by simp [c1]
lemma c6_ne (j : Fin 8) : c6 j ≠ 0 := by
  unfold c6; split_ifs <;> positivity
lemma c7_ne (j : Fin 8) : c7 j ≠ 0 := by
  unfold c7; split_ifs <;> positivity
lemma c1_low (j : Fin 8) (_ : j.val < 3) : c1 j = 1 := rfl
lemma c6_low (j : Fin 8) (h : j.val < 3) : c6 j = 1 := by
  unfold c6; rw [if_neg]; intro e; subst e; simp at h
lemma c7_low (j : Fin 8) (h : j.val < 3) : c7 j = 1 := by
  unfold c7; rw [if_neg]; intro e; subst e; simp at h

lemma dot_tr (c : Fin 8 → ℝ) (w : W) (hw : ∀ j, c j * c j = (w j : ℝ)) (p q : W) :
    dotProduct (Lc c p) (Lc c q) = ((wdot w p q : ℚ) : ℝ) := by
  simp only [dotProduct, Lc, wdot]; push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hw j]; ring
lemma w1_ok (j : Fin 8) : c1 j * c1 j = (w1 j : ℝ) := by simp [c1, w1]
lemma w6_ok (j : Fin 8) : c6 j * c6 j = (w6 j : ℝ) := by
  unfold c6 w6; split_ifs <;> simp
lemma w7_ok (j : Fin 8) : c7 j * c7 j = (w7 j : ℝ) := by
  unfold c7 w7; split_ifs <;> simp

section
variable (c : Fin 8 → ℝ) (hlow : ∀ j : Fin 8, j.val < 3 → c j = 1)
include hlow

lemma cyc_tr (t : Fin 3) (q : W) : cycleFirstThree t (Lc c q) = Lc c (cycQ t q) := by
  ext j; simp only [cycleFirstThree, cycQ, Lc]
  split_ifs with h
  · rw [hlow _ (Nat.mod_lt _ (by norm_num)), hlow j h]
  · rfl
lemma proj_tr (q : W) : rootProjection (Lc c q) = Lc c (projQ q) := by
  ext j; simp only [rootProjection, projQ, Lc]
  split_ifs with h
  · rw [hlow j h, hlow 0 (by simp), hlow 1 (by simp), hlow 2 (by simp)]; push_cast; ring
  · simp
lemma ew_tr (i : Fin 3) : externalWeight i = Lc c (ewQ i) := by
  simp only [externalWeight, ewQ, firstThreeSum, ftsQ, Lc_smul, Lc_sub, Lc_add, Lc_kq,
    hlow 0 (by simp), hlow 1 (by simp), hlow 2 (by simp), hlow ⟨i.val, by omega⟩ (by simp), one_smul]
  push_cast; rfl
end

lemma signed_tr (f : W → V) (hf : ∀ x, f (-x) = -f x) (S : Finset W) :
    signed (S.image f) = (signedQ S).image f := by
  unfold signed signedQ
  rw [Finset.image_union, Finset.image_image, Finset.image_image]
  congr 1
  exact Finset.image_congr fun x _ => by simp [hf]

lemma negImage_tr (c : Fin 8 → ℝ) (S : Finset W) :
    (S.image (Lc c)).image (fun x => -x) = (S.image (fun x => -x)).image (Lc c) := by
  rw [Finset.image_image, Finset.image_image]
  exact Finset.image_congr fun x _ => by simp [Lc_neg]

lemma differences_tr (c : Fin 8 → ℝ) (I : Finset (Fin 8)) (h : ∀ i ∈ I, c i = 1) :
    differences I = (differencesQ I).image (Lc c) := by
  unfold differences differencesQ
  rw [Finset.biUnion_image]
  refine Finset.biUnion_congr rfl fun i hi => ?_
  rw [Finset.image_image]
  refine Finset.image_congr fun j hj => ?_
  simp [Lc_sub, Lc_kq, h i hi, h j (Finset.mem_of_mem_erase hj)]

lemma dRoots_tr (c : Fin 8 → ℝ) (I : Finset (Fin 8)) (h : ∀ i ∈ I, c i = 1) :
    dRoots I = (dRootsQ I).image (Lc c) := by
  unfold dRoots dRootsQ
  rw [Finset.biUnion_image]
  refine Finset.biUnion_congr rfl fun i hi => ?_
  rw [Finset.biUnion_image]
  refine Finset.biUnion_congr rfl fun j hj => ?_
  simp [Finset.image_insert, Lc_sub, Lc_add, Lc_neg, Lc_kq, h i hi,
    h j (Finset.mem_of_mem_erase hj)]

lemma halfSums_tr (c : Fin 8 → ℝ) {m : ℕ} (a : Fin m → V) (aq : Fin m → W)
    (p : (Fin m → Bool) → Prop) (pq : (Fin m → Bool) → Prop) [DecidablePred pq]
    (hp : ∀ s, p s ↔ pq s) (ha : ∀ i, Lc c (aq i) = a i) :
    halfSums a p = (halfSumsQ aq pq).image (Lc c) := by
  unfold halfSums halfSumsQ
  rw [Finset.image_image]
  have hf : Finset.univ.filter p = Finset.univ.filter pq := by ext s; simp [hp]
  rw [hf]
  refine Finset.image_congr fun s _ => ?_
  simp [Lc_smul, Lc_sum, ha, signQ_cast]

lemma external_tr (c : Fin 8 → ℝ) (hlow : ∀ j : Fin 8, j.val < 3 → c j = 1) :
    external = externalQ.image (Lc c) :=
  differences_tr c _ (fun i hi => hlow i (by fin_cases hi <;> simp))

lemma orientedBlock_tr (c : Fin 8 → ℝ) (hlow : ∀ j : Fin 8, j.val < 3 → c j = 1)
    (BQ : Finset W) (t : Fin 3) (b : Bool) :
    orientedBlock (BQ.image (Lc c)) t b = (orientedBlockQ BQ t b).image (Lc c) := by
  unfold orientedBlock orientedBlockQ
  cases b
  · simp only [Bool.false_eq_true, if_false, Finset.image_image]
    exact Finset.image_congr fun x _ => by simp [cyc_tr c hlow, Lc_neg]
  · simp only [if_true, Finset.image_image]
    exact Finset.image_congr fun x _ => by simp [cyc_tr c hlow]

lemma piece_tr (c : Fin 8 → ℝ) (hlow : ∀ j : Fin 8, j.val < 3 → c j = 1)
    (CQ BQ : Finset W) (p : Piece) :
    piece (CQ.image (Lc c)) (BQ.image (Lc c)) p = (pieceQ CQ BQ p).image (Lc c) := by
  rcases p with (_ | _) | ⟨t, b⟩
  · exact external_tr c hlow
  · rfl
  · exact orientedBlock_tr c hlow BQ t b

lemma rootPartition_tr (c : Fin 8 → ℝ) (hlow : ∀ j : Fin 8, j.val < 3 → c j = 1)
    (hc : ∀ j, c j ≠ 0) (RQ CQ BQ : Finset W) (cs bs : ℕ) (h : rootPartitionQ RQ CQ BQ cs bs) :
    rootPartition (RQ.image (Lc c)) (CQ.image (Lc c)) (BQ.image (Lc c)) cs bs := by
  have hi := Lc_inj c hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1, Finset.biUnion_image]
    exact Finset.biUnion_congr rfl fun p _ => (piece_tr c hlow CQ BQ p).symm
  · intro i j hij
    rw [piece_tr c hlow, piece_tr c hlow, Finset.disjoint_image hi]
    exact h2 i j hij
  · rw [Finset.card_image_of_injective _ hi, h3]
  · rw [external_tr c hlow, Finset.card_image_of_injective _ hi, h4]
  · rw [Finset.card_image_of_injective _ hi, h5]
  · intro t b
    rw [orientedBlock_tr c hlow, Finset.card_image_of_injective _ hi, h6]
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    rw [proj_tr c hlow, h7 q hq, Lc_zero]
  · intro x hx
    rw [external_tr c hlow] at hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    rw [proj_tr c hlow, h8 q hq]
  · intro t b x hx
    rw [orientedBlock_tr c hlow] at hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    rw [proj_tr c hlow, h9 t b q hq]
    cases b <;> simp [ew_tr c hlow, Lc_neg]

lemma isA2_tr (c : Fin 8 → ℝ) (w : W) (hw : ∀ j, c j * c j = (w j : ℝ))
    (RQ : Finset W) (aq bq : W) (lq : ℚ) (h : isA2Q w RQ aq bq lq)
    (a b : V) (ha : a = Lc c aq) (hb : b = Lc c bq) (l : ℝ) (hl : l = (lq : ℝ)) :
    isA2 (RQ.image (Lc c)) a b l := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  subst ha hb hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1, ← signed_tr _ (Lc_neg c)]
    simp [Finset.image_insert, Lc_add]
  · rw [dot_tr c w hw, h2]
  · rw [dot_tr c w hw, h3]
  · rw [dot_tr c w hw, h4]; push_cast; ring

end G64I
namespace G64I
open QAlgorithms.Papers.Independent.Renew46.P14

lemma ewImage_tr : Finset.univ.image externalWeight = (Finset.univ.image ewQ).image (Lc c1) := by
  rw [Finset.image_image]; congr 1; funext i; exact ew_tr c1 c1_low i

lemma rootsG2_tr : rootsG2 = rootsG2Q.image (Lc c1) := by
  unfold rootsG2 rootsG2Q
  rw [Finset.image_union, ← external_tr c1 c1_low, ← signed_tr _ (Lc_neg c1), ewImage_tr]

lemma rootsF4_tr : rootsF4 = rootsF4Q.image (Lc c1) := by
  unfold rootsF4 rootsF4Q
  rw [Finset.image_union, Finset.image_union, ← signed_tr _ (Lc_neg c1), Finset.image_image,
    ← dRoots_tr c1 _ (fun _ _ => rfl),
    halfSums_tr c1 _ ![kq 0, kq 1, kq 2, kq 3] _ (fun _ => True) (fun _ => Iff.rfl)
      (fun i => by fin_cases i <;> simp [Lc_kq, c1])]
  congr 3; exact Finset.image_congr fun i _ => by simp [Lc_kq, c1]

lemma rootsE6_tr : rootsE6 = rootsE6Q.image (Lc c6) := by
  unfold rootsE6 rootsE6Q
  rw [Finset.image_union, ← dRoots_tr c6 _ (fun i hi => by fin_cases hi <;> simp [c6]),
    halfSums_tr c6 _ ![kq 0, kq 1, kq 2, kq 3, kq 4, kq 5] _ (fun s => plusCountQ 6 s % 2 = 1)
      (fun s => by rw [plusCount_eq]) (fun i => by fin_cases i <;> simp [Lc_kq, c6])]

lemma rootsE7_tr : rootsE7 = rootsE7Q.image (Lc c7) := by
  unfold rootsE7 rootsE7Q
  rw [Finset.image_union, Finset.image_union, ← signed_tr _ (Lc_neg c7),
    ← dRoots_tr c7 _ (fun i hi => by fin_cases hi <;> simp [c7]),
    halfSums_tr c7 _ ![kq 0, kq 1, kq 2, kq 3, kq 4, kq 5, kq 6] _ (fun s => plusCountQ 6 s % 2 = 0)
      (fun s => by rw [plusCount_eq]) (fun i => by fin_cases i <;> simp [Lc_kq, c7])]
  simp [Lc_kq, c7]

lemma rootsE8_tr : rootsE8 = rootsE8Q.image (Lc c1) := by
  unfold rootsE8 rootsE8Q
  rw [Finset.image_union, ← dRoots_tr c1 _ (fun _ _ => rfl),
    halfSums_tr c1 _ kq _ (fun s => plusCountQ 8 s % 2 = 0)
      (fun s => by rw [plusCount_eq]) (fun i => by simp [Lc_kq, c1])]

lemma block1_tr : block1 = block1Q.image (Lc c1) := by
  unfold block1 block1Q
  simp [Finset.image_insert, Lc_add, Lc_neg, Lc_sub, Lc_smul, Lc_kq, c1]

lemma center1_tr : center1 = center1Q.image (Lc c1) := by
  unfold center1 center1Q
  rw [← signed_tr _ (Lc_neg c1)]
  simp [Finset.image_insert, Lc_add, Lc_sub, Lc_smul, Lc_kq, c1, firstThreeSum, ftsQ]

lemma block2_tr : block2 = block2Q.image (Lc c6) := by
  unfold block2 block2Q
  simp [Finset.image_insert, Lc_add, Lc_neg, Lc_sub, Lc_smul, Lc_kq, c6]

lemma center2First_tr : center2First = center2FirstQ.image (Lc c6) := by
  unfold center2First center2FirstQ
  rw [← signed_tr _ (Lc_neg c6)]
  simp [Finset.image_insert, Lc_add, Lc_sub, Lc_smul, Lc_kq, c6, firstThreeSum, ftsQ]

lemma center2Second_tr : center2Second = center2SecondQ.image (Lc c6) := by
  unfold center2Second center2SecondQ
  rw [← signed_tr _ (Lc_neg c6)]
  simp [Finset.image_insert, Lc_add, Lc_sub, Lc_smul, Lc_kq, c6, firstThreeSum, ftsQ]

lemma center2_tr : center2 = center2Q.image (Lc c6) := by
  unfold center2 center2Q
  rw [Finset.image_union, center2First_tr, center2Second_tr]

end G64I
theorem solution :
    rootPartition rootsE6 center2 block2 12 9 ∧
    isA2 center2First (k 3 + k 4)
      ((1 / 2 : ℝ) • (firstThreeSum - k 3 - k 4 - Real.sqrt (3 : ℝ) • k 5)) 2 ∧
    isA2 center2Second (k 3 - k 4)
      ((1 / 2 : ℝ) • (firstThreeSum - k 3 + k 4 + Real.sqrt (3 : ℝ) • k 5)) 2 ∧
    (∀ x ∈ center2First, ∀ y ∈ center2Second, dotProduct x y = 0) := by
  open G64I in
  obtain ⟨q1, q2, q3, q4⟩ := qE6
  rw [rootsE6_tr, center2_tr, block2_tr, center2First_tr, center2Second_tr]
  refine ⟨rootPartition_tr c6 c6_low c6_ne _ _ _ _ _ q1,
    isA2_tr c6 w6 w6_ok _ _ _ _ q2 _ _ (by simp [Lc_add, Lc_kq, c6])
      (by simp [Lc_smul, Lc_sub, Lc_add, Lc_kq, c6, ftsQ, firstThreeSum]) _ (by norm_num),
    isA2_tr c6 w6 w6_ok _ _ _ _ q3 _ _ (by simp [Lc_sub, Lc_kq, c6])
      (by simp [Lc_smul, Lc_sub, Lc_add, Lc_kq, c6, ftsQ, firstThreeSum]) _ (by norm_num), ?_⟩
  intro x hx y hy
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  rw [dot_tr c6 w6 w6_ok, q4 p hp q hq]; simp

end

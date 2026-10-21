-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P14.e8_root_blocks
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T02:45:39.811907+00:00
-- url     : https://prove2.me/submissions/a5e68fd5-0d3d-49e8-babd-bdce1dd7c253

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P14
namespace G65Z
open scoped BigOperators
/-- integer vectors; a vector `q` represents the real vector `j ↦ q j / 6 * c j` -/
abbrev W := Fin 8 → ℤ
def eq (i : Fin 8) : W := fun j => if j = i then 1 else 0
def kq (i : Fin 8) : W := fun j => if j = i then 6 else 0
def hq (i : Fin 8) : W := fun j => if j = i then 3 else 0
def ftsQ : W := kq 0 + kq 1 + kq 2
def hftsQ : W := hq 0 + hq 1 + hq 2
def projQ (x : W) : W := fun j => if j.val < 3 then 3 * x j - (x 0 + x 1 + x 2) else 0
def ewQ (i : Fin 3) : W := fun j => if j.val < 3 then (if j.val = i.val then -4 else 2) else 0
def cycQ (c : Fin 3) (x : W) : W := fun j =>
  if j.val < 3 then x ⟨(j.val + 3 - c.val) % 3, by omega⟩ else x j
def signQ (b : Bool) : ℤ := if b then 1 else -1
def plusCountQ {m : ℕ} (r : ℕ) (s : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun i => i.val < r ∧ s i = true).card
def halfSumsQ {m : ℕ} (ah : Fin m → W) (p : (Fin m → Bool) → Prop) [DecidablePred p] : Finset W :=
  (Finset.univ.filter p).image fun s => ∑ i, signQ (s i) • ah i
def signedQ (S : Finset W) : Finset W := S ∪ S.image (fun x => -x)
def differencesQ (I : Finset (Fin 8)) : Finset W :=
  I.biUnion fun i => (I.erase i).image fun j => kq i - kq j
def dRootsQ (I : Finset (Fin 8)) : Finset W :=
  I.biUnion fun i => (I.erase i).biUnion fun j =>
    {kq i + kq j, kq i - kq j, -kq i + kq j, -kq i - kq j}
def externalQ : Finset W := differencesQ {0, 1, 2}
def rootsE6Q : Finset W := dRootsQ {0, 1, 2, 3, 4} ∪
  halfSumsQ ![hq 0, hq 1, hq 2, hq 3, hq 4, hq 5] (fun s => plusCountQ 6 s % 2 = 1)
def rootsE7Q : Finset W :=
  signedQ {kq 6} ∪ dRootsQ {0, 1, 2, 3, 4, 5} ∪
    halfSumsQ ![hq 0, hq 1, hq 2, hq 3, hq 4, hq 5, hq 6] (fun s => plusCountQ 6 s % 2 = 0)
def rootsE8Q : Finset W := dRootsQ Finset.univ ∪ halfSumsQ hq (fun s => plusCountQ 8 s % 2 = 0)
def block8Q : Finset W := {kq 1 + kq 2} ∪
  (({3, 4, 5, 6, 7} : Finset (Fin 8)).biUnion fun j => {-kq 0 + kq j, -kq 0 - kq j}) ∪
  ((Finset.univ.filter fun s : Fin 5 → Bool => plusCountQ 5 s % 2 = 0).image
    fun s => -hq 0 + hq 1 + hq 2 +
      ∑ i : Fin 5, signQ (s i) • hq ⟨i.val + 3, by omega⟩)
def center8Q : Finset W := dRootsQ {3, 4, 5, 6, 7} ∪
  signedQ ((Finset.univ.filter fun s : Fin 5 → Bool => plusCountQ 5 s % 2 = 1).image
    fun s => hftsQ +
      ∑ i : Fin 5, signQ (s i) • hq ⟨i.val + 3, by omega⟩)
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
  (∀ x ∈ C, projQ x = 0) ∧ (∀ x ∈ externalQ, projQ x = (3 : ℤ) • x) ∧
  (∀ c b, ∀ x ∈ orientedBlockQ B c b,
    projQ x = if b then (3 : ℤ) • ewQ c else -((3 : ℤ) • ewQ c))
def wdot (p q : W) : ℤ := ∑ j, p j * q j
def isA2Q (R : Finset W) (a b : W) (l : ℤ) : Prop :=
  R = signedQ {a, b, a + b} ∧ wdot a a = l ∧ wdot b b = l ∧ 2 * wdot a b = -l
instance (R : Finset W) (a b : W) (l : ℤ) : Decidable (isA2Q R a b l) := by
  unfold isA2Q; infer_instance
def rebE6Q (x : W) : W :=
  (∑ i : Fin 5, x ⟨i.val, by omega⟩ • eq ⟨i.val + 3, by omega⟩) - (x 5) • (eq 0 + eq 1 + eq 2)
def rebE7Q (x : W) : W :=
  (∑ i : Fin 5, x ⟨i.val, by omega⟩ • eq ⟨i.val + 3, by omega⟩) + x 5 • eq 0 + x 6 • (eq 1 + eq 2)
def zInnerQ : W := kq 3 + kq 4 + kq 5
def hzQ : W := hq 3 + hq 4 + hq 5
def innerBlockQ (f : Fin 3) : Finset W :=
  let a := kq ⟨f.val + 3, by omega⟩
  {-a + kq 6, -a - kq 6, -a + kq 7, -a - kq 7, zInnerQ - a} ∪
  ((Finset.univ.image fun s : Fin 3 → Bool =>
    -a + (signQ (s 0) • hftsQ + hzQ +
      signQ (s 1) • hq 6 + signQ (s 2) • hq 7)).filter fun x => x ∈ rootsE8Q)
def nestedA2Q : Fin 4 → Finset W :=
  ![externalQ, differencesQ {3, 4, 5},
    signedQ {kq 6 + kq 7, hftsQ + hzQ - hq 6 - hq 7,
      hftsQ + hzQ + hq 6 + hq 7},
    signedQ {kq 6 - kq 7, -hftsQ + hzQ - hq 6 + hq 7,
      -hftsQ + hzQ + hq 6 - hq 7}]
def nestedPieceQ : Fin 4 ⊕ ((Fin 3 ⊕ Fin 3) × Bool) → Finset W
  | .inl i => nestedA2Q i
  | .inr (.inl c, b) => orientedBlockQ block8Q c b
  | .inr (.inr f, true) => innerBlockQ f
  | .inr (.inr f, false) => (innerBlockQ f).image (fun x => -x)
end G65Z
namespace G65Z
open scoped BigOperators

lemma hs_apply {m : ℕ} (hm : m ≤ 8) (s : Fin m → Bool) (j : Fin 8) :
    (∑ i, signQ (s i) • hq (Fin.castLE hm i)) j =
      if h : j.val < m then 3 * signQ (s ⟨j.val, h⟩) else 0 := by
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, hq, smul_eq_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j.val, h⟩]
    · simp [Fin.ext_iff]; ring
    · intro b _ hb
      rw [if_neg]; · ring
      intro e; apply hb; ext; simp [Fin.ext_iff] at e ⊢; omega
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]; · ring
    intro e; apply h; rw [e]; simp

/-- sufficient condition for membership in a half-sum set -/
lemma mem_half_of {m : ℕ} (hm : m ≤ 8) (p : (Fin m → Bool) → Prop) [DecidablePred p] (x : W)
    (hx : ∀ j : Fin 8, (j.val < m → (x j = 3 ∨ x j = -3)) ∧ (m ≤ j.val → x j = 0))
    (hp : p (fun i => decide (x (Fin.castLE hm i) = 3))) :
    x ∈ halfSumsQ (fun i => hq (Fin.castLE hm i)) p := by
  unfold halfSumsQ
  refine Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩, ?_⟩
  funext j
  rw [hs_apply hm]
  split_ifs with h
  · have hc : Fin.castLE hm ⟨j.val, h⟩ = j := by ext; simp
    rw [hc]
    rcases (hx j).1 h with e | e <;> simp [e, signQ]
  · exact ((hx j).2 (by omega)).symm

lemma mem_half_iff8 (p : (Fin 8 → Bool) → Prop) [DecidablePred p] (x : W) :
    x ∈ halfSumsQ hq p ↔ (∀ j, x j = 3 ∨ x j = -3) ∧ p (fun j => decide (x j = 3)) := by
  have e : hq = fun i => hq (Fin.castLE (le_refl 8) i) := by funext i; simp
  constructor
  · intro hx
    unfold halfSumsQ at hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
    have hs' := (Finset.mem_filter.1 hs).2
    have hv : ∀ j, (∑ i, signQ (s i) • hq i) j = 3 * signQ (s j) := by
      intro j; rw [e, hs_apply (le_refl 8)]; simp
    refine ⟨fun j => ?_, ?_⟩
    · rw [hv]; cases s j <;> simp [signQ]
    · convert hs' using 1; funext j; rw [hv]; cases s j <;> simp [signQ]
  · rintro ⟨h1, h2⟩
    rw [e]
    exact mem_half_of (le_refl 8) p x (fun j => ⟨fun _ => h1 j, fun h => absurd j.isLt (by omega)⟩)
      (by convert h2 using 1; funext j; simp)

lemma mem_dRoots (I : Finset (Fin 8)) (x : W) :
    x ∈ dRootsQ I ↔ ∃ i ∈ I, ∃ j ∈ I, j ≠ i ∧
      (x = kq i + kq j ∨ x = kq i - kq j ∨ x = -kq i + kq j ∨ x = -kq i - kq j) := by
  simp only [dRootsQ, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, b, ⟨h1, h2⟩, h3⟩; exact ⟨a, ha, b, h2, h1, h3⟩
  · rintro ⟨a, ha, b, h2, h1, h3⟩; exact ⟨a, ha, b, ⟨h1, h2⟩, h3⟩

lemma dRoots_sub (I : Finset (Fin 8)) :
    dRootsQ I ⊆ ((I ×ˢ I).filter (fun p => p.1 < p.2)).biUnion
      (fun p => {kq p.1 + kq p.2, kq p.1 - kq p.2, -kq p.1 + kq p.2, -kq p.1 - kq p.2}) := by
  intro x hx
  obtain ⟨i, hi, j, hj, hji, h⟩ := (mem_dRoots I x).1 hx
  rw [Finset.mem_biUnion]
  rcases lt_or_gt_of_ne hji with hl | hl
  · refine ⟨(j, i), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hj, hi⟩, hl⟩, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases h with h | h | h | h <;> subst h
    · left; abel
    · right; right; left; abel
    · right; left; abel
    · right; right; right; abel
  · refine ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hi, hj⟩, hl⟩, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases h with h | h | h | h <;> simp [h]

lemma card_dRoots_le (I : Finset (Fin 8)) (n : ℕ)
    (hn : ((I ×ˢ I).filter (fun p => p.1 < p.2)).card = n) : (dRootsQ I).card ≤ 4 * n := by
  refine (Finset.card_le_card (dRoots_sub I)).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  rw [← hn, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun p _ => Finset.card_le_four

lemma card_half_le {m : ℕ} (ah : Fin m → W) (p : (Fin m → Bool) → Prop) [DecidablePred p] (n : ℕ)
    (hn : (Finset.univ.filter p).card = n) : (halfSumsQ ah p).card ≤ n :=
  hn ▸ Finset.card_image_le

def goodE8 (x : W) : Prop :=
  (∃ i j : Fin 8, j ≠ i ∧
      (x = kq i + kq j ∨ x = kq i - kq j ∨ x = -kq i + kq j ∨ x = -kq i - kq j)) ∨
  ((∀ j, x j = 3 ∨ x j = -3) ∧ plusCountQ 8 (fun j => decide (x j = 3)) % 2 = 0)
instance (x : W) : Decidable (goodE8 x) := by unfold goodE8; infer_instance

lemma memE8 (x : W) : x ∈ rootsE8Q ↔ goodE8 x := by
  unfold rootsE8Q goodE8
  rw [Finset.mem_union, mem_dRoots, mem_half_iff8]
  simp

set_option maxRecDepth 100000 in
lemma card_rootsE8_le : rootsE8Q.card ≤ 240 := by
  unfold rootsE8Q
  have h1 := card_dRoots_le Finset.univ 28 (by decide +kernel)
  have h2 := card_half_le hq (fun s => plusCountQ 8 s % 2 = 0) 128 (by decide +kernel)
  exact (Finset.card_union_le _ _).trans (by omega)

set_option maxRecDepth 100000 in
lemma card_rootsE6_le : rootsE6Q.card ≤ 72 := by
  unfold rootsE6Q
  have h1 := card_dRoots_le {0, 1, 2, 3, 4} 10 (by decide +kernel)
  have h2 := card_half_le ![hq 0, hq 1, hq 2, hq 3, hq 4, hq 5] (fun s => plusCountQ 6 s % 2 = 1) 32
    (by decide +kernel)
  exact (Finset.card_union_le _ _).trans (by omega)

set_option maxRecDepth 100000 in
lemma card_rootsE7_le : rootsE7Q.card ≤ 126 := by
  unfold rootsE7Q
  have h1 := card_dRoots_le {0, 1, 2, 3, 4, 5} 15 (by decide +kernel)
  have h2 := card_half_le ![hq 0, hq 1, hq 2, hq 3, hq 4, hq 5, hq 6]
    (fun s => plusCountQ 6 s % 2 = 0) 64 (by decide +kernel)
  have h3 : (signedQ {kq 6}).card ≤ 2 := by
    unfold signedQ; refine (Finset.card_union_le _ _).trans ?_; simp
  exact (Finset.card_union_le _ _).trans (by
    have := Finset.card_union_le (signedQ {kq 6}) (dRootsQ {0, 1, 2, 3, 4, 5}); omega)

/-- sufficient conditions for E6 / E7 membership -/
def goodE6 (x : W) : Prop :=
  (∃ i j : Fin 8, i.val < 5 ∧ j.val < 5 ∧ j ≠ i ∧
      (x = kq i + kq j ∨ x = kq i - kq j ∨ x = -kq i + kq j ∨ x = -kq i - kq j)) ∨
  ((∀ j : Fin 8, (j.val < 6 → (x j = 3 ∨ x j = -3)) ∧ (6 ≤ j.val → x j = 0)) ∧
    plusCountQ 6 (fun i : Fin 6 => decide (x (Fin.castLE (by norm_num) i) = 3)) % 2 = 1)
instance (x : W) : Decidable (goodE6 x) := by unfold goodE6; infer_instance

def goodE7 (x : W) : Prop :=
  x = kq 6 ∨ x = -kq 6 ∨
  (∃ i j : Fin 8, i.val < 6 ∧ j.val < 6 ∧ j ≠ i ∧
      (x = kq i + kq j ∨ x = kq i - kq j ∨ x = -kq i + kq j ∨ x = -kq i - kq j)) ∨
  ((∀ j : Fin 8, (j.val < 7 → (x j = 3 ∨ x j = -3)) ∧ (7 ≤ j.val → x j = 0)) ∧
    plusCountQ 6 (fun i : Fin 7 => decide (x (Fin.castLE (by norm_num) i) = 3)) % 2 = 0)
instance (x : W) : Decidable (goodE7 x) := by unfold goodE7; infer_instance

lemma lt5 (i : Fin 8) : i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 8)) ↔ i.val < 5 := by
  fin_cases i <;> simp
lemma lt6 (i : Fin 8) : i ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 8)) ↔ i.val < 6 := by
  fin_cases i <;> simp

lemma memE6_of (x : W) (h : goodE6 x) : x ∈ rootsE6Q := by
  unfold rootsE6Q
  rw [Finset.mem_union]
  rcases h with ⟨i, j, hi, hj, hji, h⟩ | ⟨h1, h2⟩
  · left; rw [mem_dRoots]; exact ⟨i, (lt5 i).2 hi, j, (lt5 j).2 hj, hji, h⟩
  · right
    have e : ![hq 0, hq 1, hq 2, hq 3, hq 4, hq 5] = fun i : Fin 6 => hq (Fin.castLE (by norm_num) i) := by
      funext i; fin_cases i <;> rfl
    rw [e]; exact mem_half_of _ _ x h1 h2

lemma memE7_of (x : W) (h : goodE7 x) : x ∈ rootsE7Q := by
  unfold rootsE7Q
  simp only [Finset.mem_union]
  rcases h with h | h | ⟨i, j, hi, hj, hji, h⟩ | ⟨h1, h2⟩
  · left; left; simp [signedQ, h]
  · left; left; simp [signedQ, h]
  · left; right; rw [mem_dRoots]; exact ⟨i, (lt6 i).2 hi, j, (lt6 j).2 hj, hji, h⟩
  · right
    have e : ![hq 0, hq 1, hq 2, hq 3, hq 4, hq 5, hq 6] =
        fun i : Fin 7 => hq (Fin.castLE (by norm_num) i) := by
      funext i; fin_cases i <;> rfl
    rw [e]; exact mem_half_of _ _ x h1 h2

/-- explicit inverses of the two frame changes -/
def inv6 (y : W) : W := fun j => if h : j.val < 5 then y ⟨j.val + 3, by omega⟩ else if j = 5 then -y 0 else 0
def inv7 (y : W) : W := fun j => if h : j.val < 5 then y ⟨j.val + 3, by omega⟩ else
  if j = 5 then y 0 else if j = 6 then y 1 else 0

lemma image_eq_of (R : Finset W) (f g : W → W) (S : Finset W) (n : ℕ) (hR : R.card ≤ n)
    (hS : S.card = n) (hmem : ∀ y ∈ S, g y ∈ R ∧ f (g y) = y) : S = R.image f := by
  refine Finset.eq_of_subset_of_card_le (fun y hy => Finset.mem_image.2
    ⟨g y, (hmem y hy).1, (hmem y hy).2⟩) ?_
  rw [hS]; exact Finset.card_image_le.trans hR
end G65Z
namespace G65Z
theorem rp_of (R C B : Finset W) (cs bs : ℕ)
    (hsub : ∀ p, pieceQ C B p ⊆ R)
    (hdisj : ∀ i j : Bool ⊕ (Fin 3 × Bool), i ≠ j → Disjoint (pieceQ C B i) (pieceQ C B j))
    (hR : R.card ≤ 6 + cs + 6 * bs) (hext : externalQ.card = 6) (hC : C.card = cs)
    (hB : ∀ c b, (orientedBlockQ B c b).card = bs)
    (h7 : ∀ x ∈ C, projQ x = 0) (h8 : ∀ x ∈ externalQ, projQ x = (3 : ℤ) • x)
    (h9 : ∀ c b, ∀ x ∈ orientedBlockQ B c b,
      projQ x = if b then (3 : ℤ) • ewQ c else -((3 : ℤ) • ewQ c)) :
    rootPartitionQ R C B cs bs := by
  have hU : (Finset.univ.biUnion (pieceQ C B)).card = 6 + cs + 6 * bs := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)]
    simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_three, pieceQ, hext, hC, hB]
    omega
  have hsub' : Finset.univ.biUnion (pieceQ C B) ⊆ R := Finset.biUnion_subset.2 fun p _ => hsub p
  have hEq : Finset.univ.biUnion (pieceQ C B) = R :=
    Finset.eq_of_subset_of_card_le hsub' (by omega)
  refine ⟨hEq.symm, hdisj, ?_, hext, hC, hB, h7, h8, h9⟩
  rw [← hEq, hU]
set_option maxRecDepth 100000
theorem sub8 (S : Finset W) (h : ∀ x ∈ S, goodE8 x) : S ⊆ rootsE8Q :=
  fun x hx => (memE8 x).2 (h x hx)
theorem e8s0 : ∀ x ∈ pieceQ center8Q block8Q (.inl false), goodE8 x := by decide +kernel
theorem e8s1 : ∀ x ∈ pieceQ center8Q block8Q (.inl true), goodE8 x := by decide +kernel
theorem e8s2 (b : Bool) : ∀ x ∈ pieceQ center8Q block8Q (.inr (0, b)), goodE8 x := by
  revert b; decide +kernel
theorem e8s3 (b : Bool) : ∀ x ∈ pieceQ center8Q block8Q (.inr (1, b)), goodE8 x := by
  revert b; decide +kernel
theorem e8s4 (b : Bool) : ∀ x ∈ pieceQ center8Q block8Q (.inr (2, b)), goodE8 x := by
  revert b; decide +kernel
theorem e8s (p) : pieceQ center8Q block8Q p ⊆ rootsE8Q := by
  apply sub8
  rcases p with (_ | _) | ⟨c, b⟩
  · exact e8s0
  · exact e8s1
  · fin_cases c
    · exact e8s2 b
    · exact e8s3 b
    · exact e8s4 b
def pv : Bool ⊕ (Fin 3 × Bool) → W → W
  | .inl false, x => (3 : ℤ) • x
  | .inl true, _ => 0
  | .inr (c, b), _ => if b then (3 : ℤ) • ewQ c else -((3 : ℤ) • ewQ c)
theorem sep1 : ∀ x ∈ externalQ, (3 : ℤ) • x ≠ 0 ∧
    ∀ (c : Fin 3) (b : Bool), (3 : ℤ) • x ≠ (if b then (3 : ℤ) • ewQ c else -((3 : ℤ) • ewQ c)) := by decide +kernel
theorem sep2 : ∀ (c : Fin 3) (b : Bool) (c' : Fin 3) (b' : Bool), (c, b) ≠ (c', b') →
    (if b then (3 : ℤ) • ewQ c else -((3 : ℤ) • ewQ c)) ≠
      (if b' then (3 : ℤ) • ewQ c' else -((3 : ℤ) • ewQ c')) := by decide +kernel
theorem sep3 : ∀ (c : Fin 3) (b : Bool), (if b then (3 : ℤ) • ewQ c else -((3 : ℤ) • ewQ c)) ≠ 0 := by decide +kernel
theorem disj_of (C B : Finset W)
    (h7 : ∀ x ∈ C, projQ x = 0) (h8 : ∀ x ∈ externalQ, projQ x = (3 : ℤ) • x)
    (h9 : ∀ c b, ∀ x ∈ orientedBlockQ B c b,
      projQ x = if b then (3 : ℤ) • ewQ c else -((3 : ℤ) • ewQ c)) :
    ∀ i j : Bool ⊕ (Fin 3 × Bool), i ≠ j → Disjoint (pieceQ C B i) (pieceQ C B j) := by
  have hp : ∀ p x, x ∈ pieceQ C B p → projQ x = pv p x := by
    rintro ((_ | _) | ⟨c, b⟩) x hx
    · exact h8 x hx
    · exact h7 x hx
    · exact h9 c b x hx
  have hx0 : ∀ p x, x ∈ pieceQ C B p → p = .inl false → x ∈ externalQ := by
    rintro p x hx rfl; exact hx
  intro i j hij
  rw [Finset.disjoint_left]
  intro x hi hj
  have e := (hp i x hi).symm.trans (hp j x hj)
  rcases i with (_ | _) | ⟨c, b⟩ <;> rcases j with (_ | _) | ⟨c', b'⟩
  · exact hij rfl
  · exact (sep1 x hi).1 e
  · exact (sep1 x hi).2 c' b' e
  · exact (sep1 x hj).1 e.symm
  · exact hij rfl
  · exact sep3 c' b' e.symm
  · exact (sep1 x hj).2 c b e.symm
  · exact sep3 c b e
  · exact sep2 c b c' b' (fun h => hij (by rw [Prod.mk.injEq] at h; rw [h.1, h.2])) e
theorem e8c1 : externalQ.card = 6 := by decide +kernel
theorem e8c2 : center8Q.card = 72 := by decide +kernel
theorem e8c3 : ∀ c b, (orientedBlockQ block8Q c b).card = 27 := by decide +kernel
theorem e8p1 : ∀ x ∈ center8Q, projQ x = 0 := by decide +kernel
theorem e8p2 : ∀ x ∈ externalQ, projQ x = (3 : ℤ) • x := by decide +kernel
theorem e8p3 : ∀ c b, ∀ x ∈ orientedBlockQ block8Q c b,
    projQ x = if b then (3 : ℤ) • ewQ c else -((3 : ℤ) • ewQ c) := by decide +kernel
theorem e8m6 : ∀ y ∈ center8Q, goodE6 (inv6 y) ∧ rebE6Q (inv6 y) = y := by decide +kernel
theorem e8m7 : ∀ y ∈ center8Q ∪ signedQ block8Q, goodE7 (inv7 y) ∧ rebE7Q (inv7 y) = y := by
  decide +kernel
theorem e8c7 : (center8Q ∪ signedQ block8Q).card = 126 := by decide +kernel
theorem e8r6 : center8Q = rootsE6Q.image rebE6Q :=
  image_eq_of _ _ inv6 _ 72 card_rootsE6_le e8c2
    (fun y hy => ⟨memE6_of _ (e8m6 y hy).1, (e8m6 y hy).2⟩)
theorem e8r7 : center8Q ∪ signedQ block8Q = rootsE7Q.image rebE7Q :=
  image_eq_of _ _ inv7 _ 126 card_rootsE7_le e8c7
    (fun y hy => ⟨memE7_of _ (e8m7 y hy).1, (e8m7 y hy).2⟩)
theorem qE8 : rootPartitionQ rootsE8Q center8Q block8Q 72 27 ∧
    center8Q = rootsE6Q.image rebE6Q ∧ center8Q ∪ signedQ block8Q = rootsE7Q.image rebE7Q :=
  ⟨rp_of _ _ _ _ _ e8s (disj_of _ _ e8p1 e8p2 e8p3) card_rootsE8_le e8c1 e8c2 e8c3 e8p1 e8p2 e8p3, e8r6, e8r7⟩
end G65Z
noncomputable section
open QAlgorithms.Papers.Independent.Renew46.P14
open scoped BigOperators
local instance : DecidableEq V := Classical.decEq V
attribute [local instance] Classical.propDecidable
namespace G65Z
open QAlgorithms.Papers.Independent.Renew46.P14

def Lc (c : Fin 8 → ℝ) (q : W) : V := fun j => (q j : ℝ) / 6 * c j

lemma Lc_add (c : Fin 8 → ℝ) (p q : W) : Lc c (p + q) = Lc c p + Lc c q := by
  ext j; simp [Lc]; ring
lemma Lc_neg (c : Fin 8 → ℝ) (p : W) : Lc c (-p) = -Lc c p := by
  ext j; simp [Lc]; ring
lemma Lc_sub (c : Fin 8 → ℝ) (p q : W) : Lc c (p - q) = Lc c p - Lc c q := by
  ext j; simp [Lc]; ring
lemma Lc_zsmul (c : Fin 8 → ℝ) (a : ℤ) (p : W) : Lc c (a • p) = (a : ℝ) • Lc c p := by
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
lemma Lc_hq (c : Fin 8 → ℝ) (i : Fin 8) : Lc c (hq i) = (1 / 2 : ℝ) • (c i • k i) := by
  ext j; simp only [Lc, hq, k, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · subst h; push_cast; ring
  · simp
lemma Lc_inj (c : Fin 8 → ℝ) (hc : ∀ j, c j ≠ 0) : Function.Injective (Lc c) := by
  intro p q h; ext j
  have := congrFun h j
  simp only [Lc] at this
  have h2 := mul_right_cancel₀ (hc j) this
  have h3 : (p j : ℝ) = q j := by linarith
  exact_mod_cast h3
lemma signQ_cast (b : Bool) : ((signQ b : ℤ) : ℝ) = sign b := by
  cases b <;> simp [signQ, sign]
lemma plusCount_eq {m : ℕ} (r : ℕ) (s : Fin m → Bool) : plusCount r s = plusCountQ r s := by
  unfold plusCount plusCountQ
  exact congrArg Finset.card (Finset.ext fun i => by simp only [Finset.mem_filter])
lemma sum_half {n : ℕ} (f : Fin n → ℝ) (v : Fin n → V) :
    ∑ i, f i • ((1 / 2 : ℝ) • v i) = (1 / 2 : ℝ) • ∑ i, f i • v i := by
  rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

def c1 : Fin 8 → ℝ := fun _ => 1
def c6 : Fin 8 → ℝ := fun j => if j = 5 then Real.sqrt 3 else 1
def c7 : Fin 8 → ℝ := fun j => if j = 6 then Real.sqrt 2 else 1
lemma c1_ne (j : Fin 8) : c1 j ≠ 0 := by simp [c1]
lemma c1_low (j : Fin 8) (_ : j.val < 3) : c1 j = 1 := rfl

lemma dot_tr (p q : W) :
    dotProduct (Lc c1 p) (Lc c1 q) = ((wdot p q : ℤ) : ℝ) / 36 := by
  simp only [dotProduct, Lc, wdot, c1]; push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

section
variable (c : Fin 8 → ℝ) (hlow : ∀ j : Fin 8, j.val < 3 → c j = 1)
include hlow

lemma cyc_tr (t : Fin 3) (q : W) : cycleFirstThree t (Lc c q) = Lc c (cycQ t q) := by
  ext j; simp only [cycleFirstThree, cycQ, Lc]
  split_ifs with h
  · rw [hlow _ (Nat.mod_lt _ (by norm_num)), hlow j h]
  · rfl
lemma proj_tr (q : W) : rootProjection (Lc c q) = (1 / 3 : ℝ) • Lc c (projQ q) := by
  ext j; simp only [rootProjection, projQ, Lc, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [hlow j h, hlow 0 (by simp), hlow 1 (by simp), hlow 2 (by simp)]; push_cast; ring
  · simp
lemma ew_tr (i : Fin 3) : externalWeight i = Lc c (ewQ i) := by
  have h0 := hlow 0 (by simp); have h1 := hlow 1 (by simp); have h2 := hlow 2 (by simp)
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [externalWeight, firstThreeSum, ewQ, Lc, k, h0, h1, h2] <;> norm_num
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
    (hp : ∀ s, p s ↔ pq s) (ha : ∀ i, Lc c (aq i) = (1 / 2 : ℝ) • a i) :
    halfSums a p = (halfSumsQ aq pq).image (Lc c) := by
  unfold halfSums halfSumsQ
  rw [Finset.image_image]
  have hf : Finset.univ.filter p = Finset.univ.filter pq := by ext s; simp [hp]
  rw [hf]
  refine Finset.image_congr fun s _ => ?_
  simp only [Function.comp, Lc_sum, Lc_zsmul, ha, signQ_cast, sum_half]

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

lemma third_three (c : Fin 8 → ℝ) (q : W) : (1 / 3 : ℝ) • Lc c ((3 : ℤ) • q) = Lc c q := by
  rw [Lc_zsmul, smul_smul]; norm_num

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
    rw [proj_tr c hlow, h7 q hq, Lc_zero, smul_zero]
  · intro x hx
    rw [external_tr c hlow] at hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    rw [proj_tr c hlow, h8 q hq, third_three]
  · intro t b x hx
    rw [orientedBlock_tr c hlow] at hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    rw [proj_tr c hlow, h9 t b q hq]
    cases b
    · simp only [Bool.false_eq_true, if_false, Lc_neg, smul_neg, third_three, ew_tr c hlow]
    · simp only [if_true, third_three, ew_tr c hlow]

lemma rootsE6_tr : rootsE6 = rootsE6Q.image (Lc c6) := by
  unfold rootsE6 rootsE6Q
  rw [Finset.image_union, ← dRoots_tr c6 _ (fun i hi => by fin_cases hi <;> simp [c6]),
    halfSums_tr c6 _ ![hq 0, hq 1, hq 2, hq 3, hq 4, hq 5] _ (fun s => plusCountQ 6 s % 2 = 1)
      (fun s => by rw [plusCount_eq]) (fun i => by fin_cases i <;> simp [Lc_hq, c6])]

lemma rootsE7_tr : rootsE7 = rootsE7Q.image (Lc c7) := by
  unfold rootsE7 rootsE7Q
  rw [Finset.image_union, Finset.image_union, ← signed_tr _ (Lc_neg c7),
    ← dRoots_tr c7 _ (fun i hi => by fin_cases hi <;> simp [c7]),
    halfSums_tr c7 _ ![hq 0, hq 1, hq 2, hq 3, hq 4, hq 5, hq 6] _ (fun s => plusCountQ 6 s % 2 = 0)
      (fun s => by rw [plusCount_eq]) (fun i => by fin_cases i <;> simp [Lc_hq, c7])]
  simp [Lc_kq, c7]

lemma rootsE8_tr : rootsE8 = rootsE8Q.image (Lc c1) := by
  unfold rootsE8 rootsE8Q
  rw [Finset.image_union, ← dRoots_tr c1 _ (fun _ _ => rfl),
    halfSums_tr c1 _ hq _ (fun s => plusCountQ 8 s % 2 = 0)
      (fun s => by rw [plusCount_eq]) (fun i => by simp [Lc_hq, c1])]

lemma block8_tr : block8 = block8Q.image (Lc c1) := by
  unfold block8 block8Q
  have hf : (Finset.univ.filter fun s : Fin 5 → Bool => plusCount 5 s % 2 = 0) =
      Finset.univ.filter fun s => plusCountQ 5 s % 2 = 0 := by ext s; simp [plusCount_eq]
  rw [Finset.image_union, Finset.image_union, Finset.biUnion_image, hf, Finset.image_image]
  congr 1; congr 1
  · simp [Lc_add, Lc_kq, c1]
  · refine Finset.biUnion_congr rfl fun j hj => ?_
    simp [Finset.image_insert, Lc_add, Lc_neg, Lc_sub, Lc_kq, c1]
  · refine Finset.image_congr fun s _ => ?_
    simp only [Function.comp, Lc_add, Lc_neg, Lc_sum, Lc_zsmul, Lc_hq, Lc_kq, c1, one_smul,
      signQ_cast, sum_half]
    module

lemma center8_tr : center8 = center8Q.image (Lc c1) := by
  unfold center8 center8Q
  have hf : (Finset.univ.filter fun s : Fin 5 → Bool => plusCount 5 s % 2 = 1) =
      Finset.univ.filter fun s => plusCountQ 5 s % 2 = 1 := by ext s; simp [plusCount_eq]
  rw [Finset.image_union, ← signed_tr _ (Lc_neg c1), ← dRoots_tr c1 _ (fun _ _ => rfl), hf,
    Finset.image_image]
  congr 2
  refine Finset.image_congr fun s _ => ?_
  simp only [Function.comp, Lc_add, Lc_sum, Lc_zsmul, Lc_hq, c1, one_smul, signQ_cast, sum_half,
    hftsQ, firstThreeSum]
  module

lemma rebE6_tr (q : W) : rebaseE6 (Lc c6 q) = Lc c1 (rebE6Q q) := by
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  ext j; fin_cases j <;>
    simp [rebaseE6, rebE6Q, Lc, c6, c1, k, eq, firstThreeSum, Fin.sum_univ_five, h3] <;> ring

lemma rebE7_tr (q : W) : rebaseE7 (Lc c7 q) = Lc c1 (rebE7Q q) := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  ext j; fin_cases j <;>
    simp [rebaseE7, rebE7Q, Lc, c7, c1, k, eq, Fin.sum_univ_five, h2] <;> ring

lemma rE6img : rootsE6.image rebaseE6 = (rootsE6Q.image rebE6Q).image (Lc c1) := by
  rw [rootsE6_tr, Finset.image_image, Finset.image_image]
  exact Finset.image_congr fun q _ => rebE6_tr q

lemma rE7img : rootsE7.image rebaseE7 = (rootsE7Q.image rebE7Q).image (Lc c1) := by
  rw [rootsE7_tr, Finset.image_image, Finset.image_image]
  exact Finset.image_congr fun q _ => rebE7_tr q

end G65Z
theorem solution :
    rootPartition rootsE8 center8 block8 72 27 ∧
    center8 = rootsE6.image rebaseE6 ∧
    center8 ∪ signed block8 = rootsE7.image rebaseE7 := by
  open G65Z in
  obtain ⟨q1, q2, q3⟩ := qE8
  refine ⟨?_, ?_, ?_⟩
  · rw [rootsE8_tr, center8_tr, block8_tr]
    exact rootPartition_tr c1 c1_low c1_ne _ _ _ _ _ q1
  · rw [center8_tr, rE6img, q2]
  · rw [center8_tr, block8_tr, signed_tr _ (Lc_neg c1), ← Finset.image_union, rE7img, q3]

end

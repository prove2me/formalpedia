-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P14.e8_explicit_nested_root_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T03:01:56.410992+00:00
-- url     : https://prove2.me/submissions/918b6948-1248-45e4-8163-cf111787d347

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
open scoped BigOperators
set_option maxRecDepth 100000

def innerBlockQ' (f : Fin 3) : Finset W :=
  let a := kq ⟨f.val + 3, by omega⟩
  {-a + kq 6, -a - kq 6, -a + kq 7, -a - kq 7, zInnerQ - a} ∪
  ((Finset.univ.image fun s : Fin 3 → Bool =>
    -a + (signQ (s 0) • hftsQ + hzQ +
      signQ (s 1) • hq 6 + signQ (s 2) • hq 7)).filter fun x => goodE8 x)
lemma innerBlock_eq (f : Fin 3) : innerBlockQ f = innerBlockQ' f := by
  unfold innerBlockQ innerBlockQ'
  dsimp only
  rw [Finset.filter_congr (fun x _ => memE8 x)]
def nestedPieceQ' : Fin 4 ⊕ ((Fin 3 ⊕ Fin 3) × Bool) → Finset W
  | .inl i => nestedA2Q i
  | .inr (.inl c, b) => orientedBlockQ block8Q c b
  | .inr (.inr f, true) => innerBlockQ' f
  | .inr (.inr f, false) => (innerBlockQ' f).image (fun x => -x)
lemma nestedPiece_eq (p) : nestedPieceQ p = nestedPieceQ' p := by
  rcases p with a | ⟨c | f, b⟩
  · rfl
  · rfl
  · cases b
    · show (innerBlockQ f).image _ = (innerBlockQ' f).image _; rw [innerBlock_eq]
    · exact innerBlock_eq f

def projZ (x : W) : W := fun j => if 3 ≤ j.val ∧ j.val < 6 then 3 * x j - (x 3 + x 4 + x 5) else 0
def ewZ (f : Fin 3) : W := fun j =>
  if 3 ≤ j.val ∧ j.val < 6 then (if j.val = f.val + 3 then -12 else 6) else 0
abbrev NP := Fin 4 ⊕ ((Fin 3 ⊕ Fin 3) × Bool)
/-- a cheap label determined by the piece -/
def L (x : W) : NP :=
  if projQ x = (3 : ℤ) • ewQ 0 then .inr (.inl 0, true) else
  if projQ x = (3 : ℤ) • ewQ 1 then .inr (.inl 1, true) else
  if projQ x = (3 : ℤ) • ewQ 2 then .inr (.inl 2, true) else
  if projQ x = -((3 : ℤ) • ewQ 0) then .inr (.inl 0, false) else
  if projQ x = -((3 : ℤ) • ewQ 1) then .inr (.inl 1, false) else
  if projQ x = -((3 : ℤ) • ewQ 2) then .inr (.inl 2, false) else
  if projQ x ≠ 0 then .inl 0 else
  if projZ x = ewZ 0 then .inr (.inr 0, true) else
  if projZ x = ewZ 1 then .inr (.inr 1, true) else
  if projZ x = ewZ 2 then .inr (.inr 2, true) else
  if projZ x = -ewZ 0 then .inr (.inr 0, false) else
  if projZ x = -ewZ 1 then .inr (.inr 1, false) else
  if projZ x = -ewZ 2 then .inr (.inr 2, false) else
  if projZ x ≠ 0 then .inl 1 else
  if x 6 = x 7 then .inl 2 else .inl 3

theorem nL (p : NP) : ∀ x ∈ nestedPieceQ' p, L x = p := by revert p; decide +kernel
theorem nG (p : NP) : ∀ x ∈ nestedPieceQ' p, goodE8 x := by revert p; decide +kernel
theorem nC : (Finset.univ.sum fun p : NP => (nestedPieceQ' p).card) = 240 := by decide +kernel
theorem nA2 : ∀ a, (nestedA2Q a).card = 6 := by decide +kernel
theorem nOB : ∀ c b, (orientedBlockQ block8Q c b).card = 27 := by decide +kernel
theorem nIB : ∀ f, (innerBlockQ' f).card = 9 ∧ innerBlockQ' f ⊆ center8Q := by decide +kernel
theorem nOrth : ∀ a b : Fin 4, a ≠ b → ∀ x ∈ nestedA2Q a, ∀ y ∈ nestedA2Q b, wdot x y = 0 := by
  decide +kernel
def waQ : Fin 4 → W := ![kq 0 - kq 1, kq 3 - kq 4, kq 6 + kq 7, kq 6 - kq 7]
def wbQ : Fin 4 → W := ![kq 1 - kq 2, kq 4 - kq 5, hftsQ + hzQ - hq 6 - hq 7,
  -hftsQ + hzQ - hq 6 + hq 7]
theorem nIsA2 : ∀ a, isA2Q (nestedA2Q a) (waQ a) (wbQ a) 72 := by decide +kernel
theorem nProj : ∀ c : Fin 3, ∀ p : NP, ∀ x ∈ nestedPieceQ' p, projQ x = (3 : ℤ) • ewQ c →
    p = .inr (.inl c, true) := by decide +kernel
theorem nProj2 : ∀ c : Fin 3, ∀ x ∈ orientedBlockQ block8Q c true, projQ x = (3 : ℤ) • ewQ c := by
  decide +kernel

theorem nDisj : ∀ i j : NP, i ≠ j → Disjoint (nestedPieceQ' i) (nestedPieceQ' j) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro x hi hj
  exact hij ((nL i x hi).symm.trans (nL j x hj))

theorem nUnion : rootsE8Q = Finset.univ.biUnion nestedPieceQ' := by
  have hsub : Finset.univ.biUnion nestedPieceQ' ⊆ rootsE8Q :=
    Finset.biUnion_subset.2 fun p _ x hx => (memE8 x).2 (nG p x hx)
  have hc : (Finset.univ.biUnion nestedPieceQ').card = 240 := by
    rw [Finset.card_biUnion (fun i _ j _ hij => nDisj i j hij), nC]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc]; exact card_rootsE8_le)).symm

theorem qN : rootsE8Q = Finset.univ.biUnion nestedPieceQ ∧ rootsE8Q.card = 240 ∧
  (∀ i j, i ≠ j → Disjoint (nestedPieceQ i) (nestedPieceQ j)) ∧
  (∀ a, (nestedA2Q a).card = 6) ∧ (∀ c b, (orientedBlockQ block8Q c b).card = 27) ∧
  (∀ f, (innerBlockQ f).card = 9 ∧ innerBlockQ f ⊆ center8Q) ∧
  (∀ a b : Fin 4, a ≠ b → ∀ x ∈ nestedA2Q a, ∀ y ∈ nestedA2Q b, wdot x y = 0) ∧
  (∀ a, isA2Q (nestedA2Q a) (waQ a) (wbQ a) 72) ∧
  (∀ c, rootsE8Q.filter (fun x => projQ x = (3 : ℤ) • ewQ c) = orientedBlockQ block8Q c true) := by
  have hpe : nestedPieceQ = nestedPieceQ' := funext nestedPiece_eq
  have hU := nUnion
  refine ⟨hpe ▸ hU, ?_, hpe ▸ nDisj, nA2, nOB, fun f => innerBlock_eq f ▸ nIB f, nOrth, nIsA2, ?_⟩
  · rw [hU, Finset.card_biUnion (fun i _ j _ hij => nDisj i j hij), nC]
  · intro c
    ext x
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hp⟩
      rw [hU, Finset.mem_biUnion] at hx
      obtain ⟨p, _, hxp⟩ := hx
      have := nProj c p x hxp hp
      subst this
      exact hxp
    · intro hx
      refine ⟨?_, nProj2 c x hx⟩
      rw [hU]
      exact Finset.mem_biUnion.2 ⟨.inr (.inl c, true), Finset.mem_univ _, hx⟩
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
namespace G65Z
open QAlgorithms.Papers.Independent.Renew46.P14

lemma innerBlock_tr (f : Fin 3) : innerBlock f = (innerBlockQ f).image (Lc c1) := by
  have inj := Lc_inj c1 c1_ne
  unfold innerBlock innerBlockQ
  dsimp only
  rw [Finset.image_union]
  refine congrArg₂ (· ∪ ·) ?_ ?_
  · simp [Finset.image_insert, Lc_add, Lc_neg, Lc_sub, Lc_kq, c1, zInner, zInnerQ]
  · have hi : (Finset.univ.image fun s : Fin 3 → Bool =>
        -k ⟨f.val + 3, by omega⟩ + (1 / 2 : ℝ) • (sign (s 0) • firstThreeSum + zInner +
          sign (s 1) • k 6 + sign (s 2) • k 7)) =
        (Finset.univ.image fun s : Fin 3 → Bool =>
        -kq ⟨f.val + 3, by omega⟩ + (signQ (s 0) • hftsQ + hzQ +
          signQ (s 1) • hq 6 + signQ (s 2) • hq 7)).image (Lc c1) := by
      rw [Finset.image_image]
      exact Finset.image_congr fun s _ => by
        simp only [Function.comp, Lc_add, Lc_neg, Lc_zsmul, Lc_hq, Lc_kq, c1, one_smul,
          signQ_cast, hftsQ, hzQ, firstThreeSum, zInner]
        module
    rw [hi, rootsE8_tr, Finset.filter_image,
      Finset.filter_congr (fun x _ => inj.mem_finset_image (s := rootsE8Q) (a := x))]

lemma nestedA2_tr (a : Fin 4) : nestedA2 a = (nestedA2Q a).image (Lc c1) := by
  fin_cases a
  · exact external_tr c1 c1_low
  · exact differences_tr c1 _ (fun _ _ => rfl)
  · show signed {k 6 + k 7, _, _} = (signedQ {kq 6 + kq 7, _, _}).image (Lc c1)
    rw [← signed_tr _ (Lc_neg c1)]
    have e1 : Lc c1 (hftsQ + hzQ - hq 6 - hq 7) =
        (1 / 2 : ℝ) • (firstThreeSum + zInner - k 6 - k 7) := by
      simp only [Lc_add, Lc_sub, Lc_hq, c1, one_smul, hftsQ, hzQ, firstThreeSum, zInner]; module
    have e2 : Lc c1 (hftsQ + hzQ + hq 6 + hq 7) =
        (1 / 2 : ℝ) • (firstThreeSum + zInner + k 6 + k 7) := by
      simp only [Lc_add, Lc_sub, Lc_hq, c1, one_smul, hftsQ, hzQ, firstThreeSum, zInner]; module
    simp only [Finset.image_insert, Finset.image_singleton, e1, e2, Lc_add, Lc_kq, c1, one_smul]
  · show signed {k 6 - k 7, _, _} = (signedQ {kq 6 - kq 7, _, _}).image (Lc c1)
    rw [← signed_tr _ (Lc_neg c1)]
    have e1 : Lc c1 (-hftsQ + hzQ - hq 6 + hq 7) =
        (1 / 2 : ℝ) • (-firstThreeSum + zInner - k 6 + k 7) := by
      simp only [Lc_add, Lc_sub, Lc_neg, Lc_hq, c1, one_smul, hftsQ, hzQ, firstThreeSum, zInner]
      module
    have e2 : Lc c1 (-hftsQ + hzQ + hq 6 - hq 7) =
        (1 / 2 : ℝ) • (-firstThreeSum + zInner + k 6 - k 7) := by
      simp only [Lc_add, Lc_sub, Lc_neg, Lc_hq, c1, one_smul, hftsQ, hzQ, firstThreeSum, zInner]
      module
    simp only [Finset.image_insert, Finset.image_singleton, e1, e2, Lc_sub, Lc_kq, c1, one_smul]

lemma nestedPiece_tr (p : NestedPiece) : nestedPiece p = (nestedPieceQ p).image (Lc c1) := by
  rcases p with a | ⟨c | f, b⟩
  · exact nestedA2_tr a
  · show orientedBlock block8 c b = (orientedBlockQ block8Q c b).image _
    rw [block8_tr]; exact orientedBlock_tr c1 c1_low _ c b
  · cases b
    · show (innerBlock f).image (fun x => -x) = ((innerBlockQ f).image (fun x => -x)).image (Lc c1)
      rw [innerBlock_tr, negImage_tr]
    · exact innerBlock_tr f

lemma isA2_tr (RQ : Finset W) (aq bq : W) (h : isA2Q RQ aq bq 72) :
    isA2 (RQ.image (Lc c1)) (Lc c1 aq) (Lc c1 bq) 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h4' : wdot aq bq = -36 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1, ← signed_tr _ (Lc_neg c1)]
    simp [Finset.image_insert, Lc_add]
  · rw [dot_tr, h2]; norm_num
  · rw [dot_tr, h3]; norm_num
  · rw [dot_tr, h4']; norm_num
end G65Z
theorem solution :
    rootsE8 = Finset.univ.biUnion nestedPiece ∧ rootsE8.card = 240 ∧
    (∀ i j : NestedPiece, i ≠ j → Disjoint (nestedPiece i) (nestedPiece j)) ∧
    (∀ a : Fin 4, (nestedA2 a).card = 6) ∧
    (∀ c b, (orientedBlock block8 c b).card = 27) ∧
    (∀ f : Fin 3, (innerBlock f).card = 9 ∧ innerBlock f ⊆ center8) ∧
    (∀ a b : Fin 4, a ≠ b → ∀ x ∈ nestedA2 a, ∀ y ∈ nestedA2 b, dotProduct x y = 0) ∧
    (∀ a : Fin 4, ∃ x y : V, isA2 (nestedA2 a) x y 2) ∧
    (∀ c : Fin 3, rootsE8.filter (fun x => rootProjection x = externalWeight c) =
      orientedBlock block8 c true) := by
  open G65Z in
  have inj := Lc_inj c1 c1_ne
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := qN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rootsE8_tr, q1, Finset.biUnion_image]
    exact Finset.biUnion_congr rfl fun p _ => (nestedPiece_tr p).symm
  · rw [rootsE8_tr, Finset.card_image_of_injective _ inj, q2]
  · intro i j hij
    rw [nestedPiece_tr, nestedPiece_tr, Finset.disjoint_image inj]
    exact q3 i j hij
  · intro a; rw [nestedA2_tr, Finset.card_image_of_injective _ inj, q4]
  · intro c b
    rw [block8_tr, orientedBlock_tr c1 c1_low, Finset.card_image_of_injective _ inj, q5]
  · intro f
    rw [innerBlock_tr, center8_tr, Finset.card_image_of_injective _ inj]
    exact ⟨(q6 f).1, Finset.image_subset_image (q6 f).2⟩
  · intro a b hab x hx y hy
    rw [nestedA2_tr] at hx hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    rw [dot_tr, q7 a b hab p hp q hq]; simp
  · intro a
    refine ⟨Lc c1 (waQ a), Lc c1 (wbQ a), ?_⟩
    rw [nestedA2_tr]
    exact isA2_tr _ _ _ (q8 a)
  · intro c
    have key : ∀ x : W, rootProjection (Lc c1 x) = externalWeight c ↔
        projQ x = (3 : ℤ) • ewQ c := by
      intro x
      rw [proj_tr c1 c1_low, ew_tr c1 c1_low, ← third_three c1 (ewQ c)]
      constructor
      · intro h
        have h' : Lc c1 (projQ x) = Lc c1 ((3 : ℤ) • ewQ c) := by
          have := congrArg (fun v => (3 : ℝ) • v) h
          simpa [smul_smul] using this
        exact inj h'
      · intro h; rw [h]
    rw [rootsE8_tr, Finset.filter_image, block8_tr, orientedBlock_tr c1 c1_low, ← q9 c,
      Finset.filter_congr (fun x _ => key x)]

end

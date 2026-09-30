-- Prove2me | solution 1 for RevenueManagement.optimal_allocation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T22:42:43.487984+00:00
-- url     : https://prove2.me/submissions/dd79e4a8-ae0e-455c-815e-48f8ecff151f

import Mathlib
import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

open Classical Finset

section
variable {N : ℕ} (v : Fin N → ℝ)

/-- `j` is ahead of `i` in the second-price ranking. -/
def oaAhead (i j : Fin N) : Prop := v i < v j ∨ (v j = v i ∧ j < i)

/-- The rank of `i`: the number of customers ahead of it. -/
noncomputable def oaRank (i : Fin N) : ℕ := (univ.filter (fun j => oaAhead v i j)).card

lemma oa_irrefl (i : Fin N) : ¬ oaAhead v i i := by
  unfold oaAhead; rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h

lemma oa_trans {i j k : Fin N} (hij : oaAhead v i j) (hjk : oaAhead v j k) : oaAhead v i k := by
  unfold oaAhead at *
  rcases hij with h1 | ⟨h1, h1'⟩ <;> rcases hjk with h2 | ⟨h2, h2'⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨h2.trans h1, h2'.trans h1'⟩

lemma oa_total {i j : Fin N} (hne : i ≠ j) : oaAhead v i j ∨ oaAhead v j i := by
  unfold oaAhead
  rcases lt_trichotomy (v i) (v j) with h | h | h
  · left; left; exact h
  · rcases lt_or_gt_of_ne hne with h' | h'
    · right; right; exact ⟨h, h'⟩
    · left; right; exact ⟨h.symm, h'⟩
  · right; left; exact h

/-- If `j` is ahead of `i`, `j` has strictly smaller rank. -/
lemma oa_rank_lt {i j : Fin N} (h : oaAhead v i j) : oaRank v j < oaRank v i := by
  unfold oaRank
  apply card_lt_card
  refine ⟨fun k hk => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact oa_trans v h hk
  · have := hsub (mem_filter.mpr ⟨mem_univ j, h⟩)
    simp only [mem_filter, mem_univ, true_and] at this
    exact oa_irrefl v j this

lemma oa_rank_inj : Function.Injective (oaRank v) := by
  intro i j hij
  by_contra hne
  rcases oa_total v hne with h | h
  · have := oa_rank_lt v h; omega
  · have := oa_rank_lt v h; omega

lemma oa_rank_lt_N (i : Fin N) : oaRank v i < N := by
  unfold oaRank
  calc (univ.filter (fun j => oaAhead v i j)).card < (univ : Finset (Fin N)).card := by
        apply card_lt_card
        refine ⟨subset_univ _, fun hsub => ?_⟩
        have := hsub (mem_univ i)
        simp only [mem_filter, mem_univ, true_and] at this
        exact oa_irrefl v i this
    _ = N := by simp

/-- Exactly `k` customers have rank below `k ≤ N`. -/
lemma oa_card_rank_lt {k : ℕ} (hk : k ≤ N) : (univ.filter (fun i => oaRank v i < k)).card = k := by
  have himg : univ.image (oaRank v) = range N := by
    apply eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨i, -, rfl⟩ := mem_image.mp hr
      exact mem_range.mpr (oa_rank_lt_N v i)
    · rw [card_image_of_injective _ (oa_rank_inj v)]; simp
  have : (univ.filter (fun i => oaRank v i < k)).image (oaRank v) = range k := by
    ext r
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hr
      have : r ∈ univ.image (oaRank v) := by rw [himg]; exact mem_range.mpr (by omega)
      obtain ⟨i, -, hi⟩ := mem_image.mp this
      exact ⟨i, hi ▸ hr, hi⟩
  rw [← card_image_of_injective _ (oa_rank_inj v), this, card_range]

end

lemma oa_spWins_iff {N C : ℕ} (r : ℝ) (v : Fin N → ℝ) (i : Fin N) :
    spWins N C r v i ↔ r < v i ∧ oaRank v i < C := by
  unfold spWins oaRank oaAhead
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by convert h2 using 2; ext j; simp⟩

/-- `∑_P a ≤ ∑_Q b` when `|P| ≤ |Q|`, every `a` is at most every `b`, and the `a`'s are `≥ 0`. -/
lemma oa_sum_exchange {ι : Type*} (P Q : Finset ι) (f : ι → ℝ) (hcard : P.card ≤ Q.card)
    (hle : ∀ i ∈ P, ∀ w ∈ Q, f i ≤ f w) (hnn : ∀ i ∈ P, 0 ≤ f i) (hQ : ∀ w ∈ Q, 0 ≤ f w) :
    ∑ i ∈ P, f i ≤ ∑ w ∈ Q, f w := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · simpa using sum_nonneg hQ
  · obtain ⟨i0, hi0, hmax⟩ := exists_max_image P f hP
    calc ∑ i ∈ P, f i ≤ P.card • f i0 := sum_le_card_nsmul P f (f i0) hmax
      _ ≤ Q.card • f i0 := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hnn i0 hi0)
      _ ≤ ∑ w ∈ Q, f w := card_nsmul_le_sum Q f (f i0) (fun w hw => hle i0 hi0 w hw)

theorem oa_main (V : PrivateValues)
    (hJ : MonotoneOn (virtualValue V) (Set.Icc 0 V.vbar)) (C : ℕ) (vstar : ℝ)
    (hvs : vstar ∈ Set.Icc 0 V.vbar) (hJ0 : virtualValue V vstar = 0) (v : Fin V.N → ℝ)
    (hv : ∀ i, v i ∈ Set.Icc 0 V.vbar) (y : Fin V.N → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (hC : ∑ i, y i ≤ C) :
    ∑ i, virtualValue V (v i) * y i ≤
      ∑ i, virtualValue V (v i) * (secondPriceReserve V.N C vstar).y v i := by
  set J := fun i => virtualValue V (v i) with hJdef
  -- signs of J
  have hJpos : ∀ i, vstar < v i → 0 ≤ J i := fun i h => by
    have := hJ hvs (hv i) h.le; simp only [hJdef]; linarith
  have hJneg : ∀ i, v i ≤ vstar → J i ≤ 0 := fun i h => by
    have := hJ (hv i) hvs h; simp only [hJdef]; linarith
  set Y := univ.filter (fun i => y i = 1) with hY
  set W := univ.filter (fun i => spWins V.N C vstar v i) with hW
  set Yp := Y.filter (fun i => vstar < v i) with hYp
  have hLHS : ∑ i, virtualValue V (v i) * y i = ∑ i ∈ Y, J i := by
    rw [hY, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    rcases hy i with h | h <;> simp [h, hJdef]
  have hRHS : ∑ i, virtualValue V (v i) * (secondPriceReserve V.N C vstar).y v i = ∑ i ∈ W, J i := by
    rw [hW, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    simp only [secondPriceReserve, hJdef]
    split_ifs <;> simp
  rw [hLHS, hRHS]
  -- drop the non-positive terms
  have hdrop : ∑ i ∈ Y, J i ≤ ∑ i ∈ Yp, J i := by
    rw [hYp, ← sum_filter_add_sum_filter_not Y (fun i => vstar < v i)]
    have : ∑ i ∈ Y.filter (fun i => ¬ vstar < v i), J i ≤ 0 :=
      sum_nonpos fun i hi => hJneg i (not_lt.mp (mem_filter.mp hi).2)
    linarith
  -- |Y| ≤ C
  have hYC : Y.card ≤ C := by
    have : ∑ i, y i = (Y.card : ℝ) := by
      rw [hY, card_filter, Nat.cast_sum]
      refine sum_congr rfl fun i _ => ?_
      rcases hy i with h | h <;> simp [h]
    exact_mod_cast this ▸ hC
  -- winners beat every non-winner above the reserve
  have hbeat : ∀ i ∈ Yp \ W, ∀ w ∈ W, J i ≤ J w := by
    intro i hi w hw
    simp only [mem_sdiff, hYp, mem_filter, hW, mem_univ, true_and, oa_spWins_iff] at hi hw
    have hri : C ≤ oaRank v i := by by_contra h; exact hi.2 ⟨hi.1.2, by omega⟩
    have hne : i ≠ w := by rintro rfl; omega
    rcases oa_total v hne with h | h
    · -- w ahead of i: v i ≤ v w
      have hvle : v i ≤ v w := by rcases h with h | ⟨h, _⟩ <;> [exact h.le; exact h.ge]
      exact hJ (hv i) (hv w) hvle
    · have := oa_rank_lt v h; omega
  have hWpos : ∀ w ∈ W, 0 ≤ J w := fun w hw => by
    simp only [hW, mem_filter, mem_univ, true_and, oa_spWins_iff] at hw
    exact hJpos w hw.1
  have hYppos : ∀ i ∈ Yp \ W, 0 ≤ J i := fun i hi => by
    simp only [mem_sdiff, hYp, mem_filter] at hi
    exact hJpos i hi.1.2
  -- counting
  have hcount : (Yp \ W).card ≤ (W \ Yp).card := by
    rcases (Yp \ W).eq_empty_or_nonempty with h | ⟨i0, hi0⟩
    · rw [h]; simp
    · have hi0' := hi0
      simp only [mem_sdiff, hYp, mem_filter, hW, mem_univ, true_and, oa_spWins_iff] at hi0'
      have hri : C ≤ oaRank v i0 := by by_contra h; exact hi0'.2 ⟨hi0'.1.2, by omega⟩
      have hCN : C ≤ V.N := (hri.trans (oa_rank_lt_N v i0).le)
      have hWC : C ≤ W.card := by
        rw [← oa_card_rank_lt v hCN]
        apply card_le_card
        intro a ha
        simp only [mem_filter, mem_univ, true_and] at ha
        simp only [hW, mem_filter, mem_univ, true_and, oa_spWins_iff]
        refine ⟨?_, ha⟩
        have hne : a ≠ i0 := by rintro rfl; omega
        rcases oa_total v hne with h | h
        · have := oa_rank_lt v h; omega
        · have hvle : v i0 ≤ v a := by rcases h with h | ⟨h, _⟩ <;> [exact h.le; exact h.ge]
          linarith [hi0'.1.2]
      have h1 := card_sdiff_add_card_inter Yp W
      have h2 := card_sdiff_add_card_inter W Yp
      have hYpY : Yp.card ≤ Y.card := card_filter_le _ _
      rw [inter_comm] at h2
      omega
  -- assemble
  have hsplitY := sum_sdiff (s₁ := Yp ∩ W) (s₂ := Yp) (f := J) inter_subset_left
  have hsplitW := sum_sdiff (s₁ := Yp ∩ W) (s₂ := W) (f := J) inter_subset_right
  have hsd1 : Yp \ (Yp ∩ W) = Yp \ W := by ext; simp
  have hsd2 : W \ (Yp ∩ W) = W \ Yp := by ext; simp
  rw [hsd1] at hsplitY; rw [hsd2] at hsplitW
  have hex := oa_sum_exchange (Yp \ W) (W \ Yp) J hcount
    (fun i hi w hw => hbeat i hi w (mem_sdiff.mp hw).1) hYppos
    (fun w hw => hWpos w (mem_sdiff.mp hw).1)
  linarith

end RevenueManagement

open RevenueManagement

theorem solution (V : PrivateValues) (hV : V.IsRegular)
    (hJ : MonotoneOn (virtualValue V) (Set.Icc 0 V.vbar)) (C : ℕ) (vstar : ℝ)
    (hvs : vstar ∈ Set.Icc 0 V.vbar) (hJ0 : virtualValue V vstar = 0) (v : Fin V.N → ℝ)
    (hv : ∀ i, v i ∈ Set.Icc 0 V.vbar) (y : Fin V.N → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (hC : ∑ i, y i ≤ C) :
    ∑ i, virtualValue V (v i) * y i ≤
      ∑ i, virtualValue V (v i) * (secondPriceReserve V.N C vstar).y v i :=
  oa_main V hJ C vstar hvs hJ0 v hv y hy hC

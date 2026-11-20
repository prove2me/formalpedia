-- Prove2me | solution 1 for RandomSizeStable.Stability.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:38:24.171941+00:00
-- url     : https://prove2.me/submissions/6a5ea5f9-eada-4c86-8774-1a6f9dcce31f

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankBlocks
import Definitions.Def_RandomSizeStable_Stability_Stability
import Theorems.Thm_RandomSizeStable_Stability_lemma_3
import Theorems.Thm_RandomSizeStable_Stability_lemma_4

section
set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion RandomSizeStable.Stability

namespace RandomSizeStable.Dev.Common

/-- the factor attached to a draw `b` at label level `s`. -/
noncomputable def fac {V C : Type} (E : Election V C) (v : V) (c : C) (s : ℝ) (b : C) : ℝ := by
  classical
  exact if E.prefers v b c then 0 else if b = c then s else 1

theorem tupleWin_eq {V C : Type} (E : Election V C) (v : V) (c : C) {k : ℕ}
    (draws : Fin k → C) :
    tupleWin E v c draws = ∫ s in (0 : ℝ)..1, ∏ i, fac E v c s (draws i) := by
  classical
  unfold tupleWin
  by_cases h : ∃ i, E.prefers v (draws i) c
  · have h0 := h
    obtain ⟨i, hi⟩ := h0
    have : ∀ s : ℝ, ∏ i, fac E v c s (draws i) = 0 := fun s =>
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [fac, hi])
    simp only [this, h]
    simp
  · have h' : ∀ i, ¬ E.prefers v (draws i) c := fun i hi => h ⟨i, hi⟩
    have : ∀ s : ℝ, ∏ i, fac E v c s (draws i) =
        s ^ (Finset.univ.filter (fun i => draws i = c)).card := fun s => by
      simp only [fac, h', if_false]
      rw [Finset.prod_ite]
      simp
    simp only [this, h, if_false, integral_pow]
    simp

theorem fac_cont {V C : Type} (E : Election V C) (v : V) (c : C) (b : C) :
    Continuous (fun s : ℝ => fac E v c s b) := by
  unfold fac
  split_ifs <;> fun_prop

theorem sum_draws_eq {V C : Type} [Fintype C] (E : Election V C) (v : V) (c : C)
    (P : C → ℝ) (k : ℕ) :
    ∑ draws : Fin k → C, (∏ i, P (draws i)) * tupleWin E v c draws =
      ∫ s in (0 : ℝ)..1, (leftRank E P v c + s * P c) ^ k := by
  classical
  have := E.isStrictTotalOrder v
  have h1 : ∀ s : ℝ, ∑ b, P b * fac E v c s b = leftRank E P v c + s * P c := by
    intro s
    unfold leftRank
    have : ∀ b, P b * fac E v c s b =
        (if E.prefers v c b then P b else 0) + (if b = c then s * P c else 0) := by
      intro b
      unfold fac
      rcases trichotomous_of (E.prefers v) b c with h | h | h
      · have h2 : ¬ E.prefers v c b := asymm h
        have h3 : b ≠ c := fun e => (irrefl_of (E.prefers v) c) (e ▸ h)
        simp [h, h2, h3]
      · subst h
        simp [irrefl_of (E.prefers v) b, mul_comm]
      · have h2 : ¬ E.prefers v b c := asymm h
        have h3 : b ≠ c := fun e => (irrefl_of (E.prefers v) c) (e ▸ h)
        simp [h, h2, h3]
    simp only [this, Finset.sum_add_distrib]
    rw [Finset.sum_filter]
    simp
  have h2 : ∀ draws : Fin k → C, (∏ i, P (draws i)) * tupleWin E v c draws =
      ∫ s in (0 : ℝ)..1, ∏ i, (P (draws i) * fac E v c s (draws i)) := by
    intro draws
    rw [tupleWin_eq, ← intervalIntegral.integral_const_mul]
    congr 1
    ext s
    rw [Finset.prod_mul_distrib]
  simp only [h2]
  rw [← intervalIntegral.integral_finsetSum]
  · congr 1
    ext s
    rw [← h1 s, Finset.sum_pow']
    simp
  · intro draws _
    apply Continuous.intervalIntegrable
    have := fac_cont E v c
    fun_prop

theorem D_summable (D : PMF ℕ+) : Summable (fun k : ℕ+ => (D k).toReal) :=
  ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)

theorem pgf_hasSum (D : PMF ℕ+) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    HasSum (fun k : ℕ+ => (D k).toReal * t ^ (k : ℕ)) (pgf D t) := by
  have : Summable (fun k : ℕ+ => (D k).toReal * t ^ (k : ℕ)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (D_summable D)
    · exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg h0 _)
    · exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ h0 h1)
  exact this.hasSum

theorem exch (D : PMF ℕ+) (r z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z) (hrz : r + z ≤ 1) :
    HasSum (fun k : ℕ+ => (D k).toReal * ∫ s in (0 : ℝ)..1, (r + s * z) ^ (k : ℕ))
      (∫ s in (0 : ℝ)..1, pgf D (r + s * z)) := by
  have hx : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ r + s * z ∧ r + s * z ≤ 1 := by
    intro s hs
    refine ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 1)
    (F := fun (k : ℕ+) (s : ℝ) => (D k).toReal * (r + s * z) ^ (k : ℕ))
    (f := fun s => pgf D (r + s * z))
    (fun k _ => (D k).toReal)
    (fun k => by
      apply Continuous.aestronglyMeasurable
      fun_prop)
    (fun k => Filter.Eventually.of_forall (fun t ht => by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le, ht.2⟩
      obtain ⟨h0, h1⟩ := hx t ht'
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg h0 _))]
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ h0 h1)))
    (Filter.Eventually.of_forall (fun t _ => D_summable D))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t ht => by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le, ht.2⟩
      obtain ⟨h0, h1⟩ := hx t ht'
      exact pgf_hasSum D h0 h1))
  simpa [intervalIntegral.integral_const_mul] using this

theorem leftRank_bounds {V C : Type} [Fintype C] (E : Election V C) (v : V) (c : C)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) :
    0 ≤ leftRank E P v c ∧ 0 ≤ P c ∧ leftRank E P v c + P c ≤ 1 := by
  classical
  have := E.isStrictTotalOrder v
  refine ⟨Finset.sum_nonneg (fun b _ => hP.1 b), hP.1 c, ?_⟩
  unfold leftRank
  have hc : c ∉ Finset.univ.filter (fun b => E.prefers v c b) := by
    simp [irrefl_of (E.prefers v) c]
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (f := P) (Finset.subset_univ (insert c (Finset.univ.filter (fun b => E.prefers v c b))))
    (fun b _ _ => hP.1 b)
  rw [Finset.sum_insert hc, hP.2] at h
  linarith

theorem comparison_eq {V C : Type} [Fintype C] (D : PMF ℕ+) (E : Election V C) (v : V) (c : C)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) :
    comparison D E P v c = ∫ s in (0 : ℝ)..1, pgf D (leftRank E P v c + s * P c) := by
  obtain ⟨h0, h1, h2⟩ := leftRank_bounds E v c P hP
  refine ((exch D _ _ h0 h1 h2).tsum_eq.symm.trans ?_).symm
  unfold comparison
  congr 1
  ext k
  rw [sum_draws_eq]

end RandomSizeStable.Dev.Common
end

section
set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion RandomSizeStable.Stability
open Classical
open Classical

namespace RandomSizeStable.Dev.L5

/-- mass of a set of candidates -/
noncomputable def pm {C : Type} [Fintype C] (P : C → ℝ) (H : Set C) : ℝ := by
  classical
  exact ∑ c, if c ∈ H then P c else 0

theorem pm_nonneg {C : Type} [Fintype C] (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (H : Set C) :
    0 ≤ pm P H := by
  classical
  unfold pm
  exact Finset.sum_nonneg (fun c _ => by split_ifs <;> simp [hP.1 c])

theorem pm_le_one {C : Type} [Fintype C] (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (H : Set C) :
    pm P H ≤ 1 := by
  classical
  unfold pm
  calc _ ≤ ∑ c, P c := Finset.sum_le_sum (fun c _ => by split_ifs <;> simp [hP.1 c])
    _ = 1 := hP.2

theorem pm_empty {C : Type} [Fintype C] (P : C → ℝ) : pm P (∅ : Set C) = 0 := by
  classical
  simp [pm]

section order

variable {V C : Type} [Fintype C] (E : Election V C) (P : C → ℝ) (v : V)

theorem lr_ge {c c' : C} (hP : P ∈ stdSimplex ℝ C) (h : E.prefers v c c') :
    leftRank E P v c' + P c' ≤ leftRank E P v c := by
  classical
  have := E.isStrictTotalOrder v
  unfold leftRank
  have hc : c' ∉ Finset.univ.filter (fun b => E.prefers v c' b) := by
    simp [irrefl_of (E.prefers v) c']
  rw [add_comm, ← Finset.sum_insert hc]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rcases hb with rfl | hb
    · exact h
    · exact trans_of (E.prefers v) h hb
  · intro b _ _; exact hP.1 b

theorem blocks_disjoint (hP : P ∈ stdSimplex ℝ C) {c c' : C} (hne : c ≠ c') :
    Disjoint (rankBlock E P v c) (rankBlock E P v c') := by
  have := E.isStrictTotalOrder v
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [rankBlock, Set.mem_Ico] at hx hx'
  rcases trichotomous_of (E.prefers v) c c' with h | h | h
  · have := lr_ge E P v hP h
    linarith [hx.1, hx'.2]
  · exact hne h
  · have := lr_ge E P v hP h
    linarith [hx.2, hx'.1]

theorem measurableSet_markedRegion (H : Set C) : MeasurableSet (markedRegion E P v H) := by
  unfold markedRegion
  exact (Set.toFinite H).measurableSet_biUnion (fun c _ => measurableSet_Ico)

theorem markedRegion_eq (H : Set C) : markedRegion E P v H =
    ⋃ c ∈ (by classical exact Finset.univ.filter (fun c => c ∈ H) : Finset C),
      rankBlock E P v c := by
  classical
  ext x; simp [markedRegion]

theorem volume_markedRegion (hP : P ∈ stdSimplex ℝ C) (H : Set C) :
    volume (markedRegion E P v H) = ENNReal.ofReal (pm P H) := by
  classical
  rw [markedRegion_eq, measure_biUnion_finset]
  · simp only [rankBlock, Real.volume_Ico]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · unfold pm
      rw [← Finset.sum_filter]
      congr 1
      apply Finset.sum_congr rfl
      intro c _; ring_nf
    · intro c _; exact hP.1 c |> fun h => by simpa using h
  · intro c _ c' _ hne
    exact blocks_disjoint E P v hP hne
  · intro c _; exact measurableSet_Ico

theorem card_worse_lt {c c' : C} (h : E.prefers v c c') :
    (Finset.univ.filter (fun b => E.prefers v c' b)).card <
      (Finset.univ.filter (fun b => E.prefers v c b)).card := by
  classical
  have := E.isStrictTotalOrder v
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨c', ?_, ?_⟩
    · simp [h]
    · simp [irrefl_of (E.prefers v) c']
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact trans_of (E.prefers v) h hb

theorem tiling (hP : P ∈ stdSimplex ℝ C) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∃ c, leftRank E P v c ≤ x ∧ x < leftRank E P v c + P c := by
  classical
  have hso := E.isStrictTotalOrder v
  by_contra hcon
  push Not at hcon
  set worse : C → Finset C := fun c => Finset.univ.filter (fun b => E.prefers v c b) with hworse
  have hne : Nonempty C := by
    by_contra hC
    rw [not_nonempty_iff] at hC
    have := hP.2
    simp at this
  -- worst candidate
  obtain ⟨c0, -, hc0⟩ := Finset.exists_min_image Finset.univ (fun c => (worse c).card)
    Finset.univ_nonempty
  have hw0 : worse c0 = ∅ := by
    by_contra hne0
    obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hne0
    have h1 : E.prefers v c0 b := by simpa [hworse] using hb
    have := card_worse_lt E v h1
    have := hc0 b (Finset.mem_univ _)
    simp only [hworse] at *
    omega
  have hr0 : leftRank E P v c0 = 0 := by
    unfold leftRank
    have : Finset.univ.filter (fun b => E.prefers v c0 b) = ∅ := hw0
    rw [this]; simp
  set S : Finset C := Finset.univ.filter (fun c => leftRank E P v c ≤ x) with hS
  have hSne : S.Nonempty := ⟨c0, by simp [hS, hr0, hx0]⟩
  obtain ⟨c, hcS, hcmax⟩ := Finset.exists_max_image S (fun c => (worse c).card) hSne
  have hcx : leftRank E P v c ≤ x := by simpa [hS] using hcS
  have hcx2 := hcon c hcx
  set W' : Finset C := insert c (worse c) with hW'
  have hcnot : c ∉ worse c := by simp [hworse, irrefl_of (E.prefers v) c]
  have hsumW : ∑ b ∈ W', P b = leftRank E P v c + P c := by
    rw [hW', Finset.sum_insert hcnot]; unfold leftRank; simp [hworse]; ring
  set U : Finset C := Finset.univ.filter (fun b => E.prefers v b c) with hU
  have hUne : U.Nonempty := by
    by_contra hUe
    have hUe' : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUe
    have hall : W' = Finset.univ := by
      ext b
      simp only [hW', Finset.mem_insert, hworse, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      by_contra hb
      push Not at hb
      rcases trichotomous_of (E.prefers v) b c with h | h | h
      · have : b ∈ U := by simp [hU, h]
        rw [hUe'] at this; simp at this
      · exact hb.1 h
      · exact hb.2 h
    have : ∑ b ∈ W', P b = 1 := by rw [hall]; exact hP.2
    linarith
  obtain ⟨c', hc'U, hc'min⟩ := Finset.exists_min_image U (fun c => (worse c).card) hUne
  have hc'c : E.prefers v c' c := by simpa [hU] using hc'U
  have hwc' : worse c' = W' := by
    ext b
    simp only [hW', Finset.mem_insert, hworse, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hb
      rcases trichotomous_of (E.prefers v) b c with h | h | h
      · exact absurd (hc'min b (by simp [hU, h])) (by
          have := card_worse_lt E v hb
          simp only [hworse]; omega)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | hb)
      · exact hc'c
      · exact trans_of (E.prefers v) hc'c hb
  have hrank' : leftRank E P v c' = leftRank E P v c + P c := by
    have h1 : leftRank E P v c' = ∑ b ∈ worse c', P b := rfl
    rw [h1, hwc', hsumW]
  have hc'S : c' ∈ S := by simp [hS, hrank', hcx2]
  have := hcmax c' hc'S
  have := card_worse_lt E v hc'c
  simp only [hworse] at *
  omega

end order

section cuts

variable {V C : Type} [Fintype C] (E : Election V C) (P : C → ℝ) (v : V)

theorem lowerCut_nonneg (hP : P ∈ stdSimplex ℝ C) (H : Set C) : 0 ≤ lowerCut E P v H := by
  unfold lowerCut
  exact Finset.sum_nonneg (fun c _ => by split_ifs <;> simp [hP.1 c])

theorem lowerCut_empty : lowerCut E P v (∅ : Set C) = 0 := by
  have := E.isStrictTotalOrder v
  unfold lowerCut
  apply Finset.sum_eq_zero
  intro c _
  rw [if_neg]
  intro h
  exact irrefl_of (E.prefers v) c (h c (Set.notMem_empty c))

theorem lowerCut_le_pm (hP : P ∈ stdSimplex ℝ C) (H : Set C) : lowerCut E P v H ≤ pm P H := by
  have := E.isStrictTotalOrder v
  unfold lowerCut pm
  apply Finset.sum_le_sum
  intro c _
  by_cases h : ∀ j, j ∉ H → E.prefers v j c
  · have hc : c ∈ H := by
      by_contra hc
      exact irrefl_of (E.prefers v) c (h c hc)
    rw [if_pos h]; simp [hc]
  · rw [if_neg h]; split_ifs <;> simp [hP.1 c]

theorem lowerCut_le_rank (hP : P ∈ stdSimplex ℝ C) (H : Set C) (o : C) (ho : o ∉ H) :
    lowerCut E P v H ≤ leftRank E P v o := by
  unfold lowerCut leftRank
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro c _
  by_cases h : ∀ j, j ∉ H → E.prefers v j c
  · rw [if_pos h]; simp [h o ho]
  · rw [if_neg h]; split_ifs <;> simp [hP.1 c]

theorem Ioo_subset_markedRegion (hP : P ∈ stdSimplex ℝ C) (H : Set C) :
    Set.Ioo 0 (lowerCut E P v H) ⊆ markedRegion E P v H := by
  have hso := E.isStrictTotalOrder v
  intro x hx
  have hlt1 : x < 1 := lt_of_lt_of_le hx.2 ((lowerCut_le_pm E P v hP H).trans (pm_le_one P hP H))
  obtain ⟨c, hc1, hc2⟩ := tiling E P v hP x hx.1.le hlt1
  have hcQ : ∀ j, j ∉ H → E.prefers v j c := by
    by_contra hQ
    push Not at hQ
    obtain ⟨j, hjH, hjc⟩ := hQ
    have hle : lowerCut E P v H ≤ leftRank E P v c := by
      unfold lowerCut leftRank
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro q _
      by_cases h : ∀ j, j ∉ H → E.prefers v j q
      · have hjq := h j hjH
        have : E.prefers v c q := by
          rcases trichotomous_of (E.prefers v) j c with h1 | h1 | h1
          · exact absurd h1 hjc
          · exact h1 ▸ hjq
          · exact trans_of (E.prefers v) h1 hjq
        rw [if_pos h]; simp [this]
      · rw [if_neg h]; split_ifs <;> simp [hP.1 q]
    linarith [hx.2]
  have hcH : c ∈ H := by
    by_contra hcH
    exact irrefl_of (E.prefers v) c (hcQ c hcH)
  exact Set.mem_iUnion₂.mpr ⟨c, hcH, ⟨hc1, hc2⟩⟩

variable [Nonempty C]

theorem upperCut_nonneg (hP : P ∈ stdSimplex ℝ C) (H : Set C) : 0 ≤ upperCut E P v H := by
  unfold upperCut
  obtain ⟨c⟩ := ‹Nonempty C›
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ c))
  have := (RandomSizeStable.Dev.Common.leftRank_bounds E v c P hP)
  split_ifs <;> linarith [this.1, this.2.1]

theorem upperCut_le_one (hP : P ∈ stdSimplex ℝ C) (H : Set C) : upperCut E P v H ≤ 1 := by
  unfold upperCut
  apply Finset.sup'_le
  intro c _
  have := (RandomSizeStable.Dev.Common.leftRank_bounds E v c P hP)
  split_ifs <;> linarith [this.2.2]

theorem upperCut_empty : upperCut E P v (∅ : Set C) = 0 := by
  unfold upperCut
  apply le_antisymm
  · apply Finset.sup'_le
    intro c _
    simp
  · obtain ⟨c⟩ := ‹Nonempty C›
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ c))
    simp

theorem markedRegion_subset_Icc (hP : P ∈ stdSimplex ℝ C) (H : Set C) :
    markedRegion E P v H ⊆ Set.Icc 0 (upperCut E P v H) := by
  intro x hx
  obtain ⟨c, hcH, hxc⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨h1, h2⟩ := hxc
  have hb := RandomSizeStable.Dev.Common.leftRank_bounds E v c P hP
  have hPc : 0 < P c := by linarith
  refine ⟨le_trans hb.1 h1, ?_⟩
  have : leftRank E P v c + P c ≤ upperCut E P v H := by
    unfold upperCut
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ c))
    simp [hcH, hPc]
  linarith

theorem pm_le_upperCut (hP : P ∈ stdSimplex ℝ C) (H : Set C) : pm P H ≤ upperCut E P v H := by
  have h1 := volume_markedRegion E P v hP H
  have h2 := measure_mono (μ := volume) (markedRegion_subset_Icc E P v hP H)
  rw [h1, Real.volume_Icc, sub_zero] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (upperCut_nonneg E P v hP H)).mp h2

end cuts

section pgfs

open RandomSizeStable.Dev

variable (D : PMF ℕ+)

theorem pgf_monoOn : MonotoneOn (pgf D) (Set.Icc 0 1) := by
  intro s hs t ht hst
  refine hasSum_le (fun k => ?_) (Common.pgf_hasSum D hs.1 hs.2) (Common.pgf_hasSum D ht.1 ht.2)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1 hst _) ENNReal.toReal_nonneg

theorem pgf_integrableOn : IntegrableOn (pgf D) (Set.Icc 0 1) :=
  (pgf_monoOn D).integrableOn_isCompact isCompact_Icc

theorem benchmark_eq : benchmark D = primitive D 1 := by
  have := Common.exch D 0 1 le_rfl zero_le_one (by norm_num)
  simp only [zero_add, mul_one] at this
  unfold benchmark primitive
  rw [← this.tsum_eq]
  congr 1; ext k
  rw [integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
  rw [div_eq_mul_inv, mul_comm]
  push_cast
  ring

variable {V C : Type} [Fintype C] (E : Election V C) (P : C → ℝ) (v : V)

theorem integral_block (hP : P ∈ stdSimplex ℝ C) (c : C) :
    ∫ u in rankBlock E P v c, pgf D u = P c * comparison D E P v c := by
  obtain ⟨h0, h1, h2⟩ := Common.leftRank_bounds E v c P hP
  rcases h1.eq_or_lt with h | h
  · simp [rankBlock, ← h]
  · rw [Common.comparison_eq D E v c P hP]
    have := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) (pgf D) h.ne'
      (leftRank E P v c)
    simp only [mul_zero, zero_add, mul_one] at this
    have h3 : ∫ s in (0:ℝ)..1, pgf D (leftRank E P v c + s * P c) =
        ∫ s in (0:ℝ)..1, pgf D (P c * s + leftRank E P v c) := by
      congr 1; ext s; rw [add_comm, mul_comm]
    rw [h3, this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ h.ne', one_mul]
    unfold rankBlock
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    rw [add_comm]

theorem rankBlock_subset (hP : P ∈ stdSimplex ℝ C) (c : C) :
    rankBlock E P v c ⊆ Set.Ico 0 1 := by
  obtain ⟨h0, h1, h2⟩ := Common.leftRank_bounds E v c P hP
  intro x hx
  exact ⟨le_trans h0 hx.1, lt_of_lt_of_le hx.2 h2⟩

theorem integral_marked (hP : P ∈ stdSimplex ℝ C) (H : Set C) :
    ∫ u in markedRegion E P v H, (pgf D u - benchmark D) =
      ∑ c, if c ∈ H then P c * (comparison D E P v c - benchmark D) else 0 := by
  rw [markedRegion_eq, integral_biUnion_finset]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs
    · have hi : IntegrableOn (pgf D) (rankBlock E P v c) :=
        (pgf_integrableOn D).mono_set (fun x hx => by
          have := rankBlock_subset E P v hP c hx
          exact ⟨this.1, this.2.le⟩)
      rw [integral_sub hi (integrableOn_const (by simp [rankBlock]))]
      rw [integral_block D E P v hP c]
      simp [rankBlock, Measure.real, (Common.leftRank_bounds E v c P hP).2.1]
      ring
    · rfl
  · intro c _; exact measurableSet_Ico
  · intro c _ c' _ hne
    exact blocks_disjoint E P v hP hne
  · intro c _
    have hi : IntegrableOn (pgf D) (rankBlock E P v c) :=
      (pgf_integrableOn D).mono_set (fun x hx => by
        have := rankBlock_subset E P v hP c hx
        exact ⟨this.1, this.2.le⟩)
    exact hi.sub (integrableOn_const (by simp [rankBlock]))

theorem markedRegion_univ (hP : P ∈ stdSimplex ℝ C) :
    markedRegion E P v Set.univ = Set.Ico 0 1 := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨c, _, hxc⟩ := Set.mem_iUnion₂.mp hx
    exact rankBlock_subset E P v hP c hxc
  · intro x hx
    obtain ⟨c, h1, h2⟩ := tiling E P v hP x hx.1 hx.2
    exact Set.mem_iUnion₂.mpr ⟨c, Set.mem_univ _, ⟨h1, h2⟩⟩

theorem selfplay (hP : P ∈ stdSimplex ℝ C) :
    ∑ c, P c * (comparison D E P v c - benchmark D) = 0 := by
  have h := integral_marked D E P v hP Set.univ
  rw [markedRegion_univ E P v hP] at h
  simp only [Set.mem_univ, if_true] at h
  rw [← h]
  have hi : IntegrableOn (pgf D) (Set.Ico 0 1) :=
    (pgf_integrableOn D).mono_set Set.Ico_subset_Icc_self
  rw [integral_sub hi (integrableOn_const (μ := volume) (s := Set.Ico (0:ℝ) 1) (by simp))]
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have := benchmark_eq D
  unfold primitive at this
  simp [Measure.real, ← this]

theorem pgf_le_comparison (hP : P ∈ stdSimplex ℝ C) (c : C) :
    pgf D (leftRank E P v c) ≤ comparison D E P v c := by
  obtain ⟨h0, h1, h2⟩ := Common.leftRank_bounds E v c P hP
  rw [Common.comparison_eq D E v c P hP]
  have hmono : MonotoneOn (fun s : ℝ => pgf D (leftRank E P v c + s * P c)) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    intro s hs t ht hst
    apply pgf_monoOn D
    · exact ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
    · exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    · nlinarith
  have hint : IntervalIntegrable (fun s : ℝ => pgf D (leftRank E P v c + s * P c)) volume 0 1 :=
    hmono.intervalIntegrable
  calc pgf D (leftRank E P v c) = ∫ s in (0:ℝ)..1, pgf D (leftRank E P v c) := by simp
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const hint
      intro s hs
      apply pgf_monoOn D
      · exact ⟨h0, by linarith⟩
      · exact ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
      · nlinarith [hs.1]

end pgfs

section marks

variable {V C : Type} [Fintype C] [Nonempty C]
  (d : V ⊕ C → V ⊕ C → ℝ) (o : C)

theorem measurableSet_marked_eq (S : Set C) : MeasurableSet {t : ℝ | marked d o t = S} := by
  have : {t : ℝ | marked d o t = S} =
      ⋂ c, {t : ℝ | (t < d (Sum.inr o) (Sum.inr c)) ↔ c ∈ S} := by
    ext t; simp [marked, Set.ext_iff]
  rw [this]
  refine MeasurableSet.iInter (fun c => ?_)
  by_cases hc : c ∈ S
  · simp only [hc, iff_true]; exact measurableSet_Iio
  · simp only [hc, iff_false, not_lt]; exact measurableSet_Ici

theorem measurable_marked (F : Set C → ℝ) : Measurable (fun t : ℝ => F (marked d o t)) := by
  have : (fun t : ℝ => F (marked d o t)) =
      fun t => ∑ S : Set C, if marked d o t = S then F S else 0 := by
    ext t; simp
  rw [this]
  exact Finset.measurable_sum _ (fun S _ =>
    Measurable.ite (measurableSet_marked_eq d o S) measurable_const measurable_const)

theorem marked_eq_empty {t : ℝ} (ht : maxDistance d o ≤ t) : marked d o t = ∅ := by
  ext c
  simp only [marked, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
  exact le_trans (Finset.le_sup' (fun c => d (Sum.inr o) (Sum.inr c)) (Finset.mem_univ c)) ht

theorem integrableOn_marked (F : Set C → ℝ) (hF : F ∅ = 0) :
    IntegrableOn (fun t : ℝ => F (marked d o t)) (Set.Ioi 0) := by
  set T := maxDistance d o
  have h1 : IntegrableOn (fun t : ℝ => F (marked d o t)) (Set.Ioc 0 T) := by
    refine Measure.integrableOn_of_bounded (M := ∑ S : Set C, |F S|) (by simp)
      (measurable_marked d o F).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun S => |F S|) (fun S _ => abs_nonneg _) (Finset.mem_univ _)
  have h2 : IntegrableOn (fun t : ℝ => F (marked d o t)) (Set.Ioi T) := by
    refine (integrableOn_zero (μ := volume) (s := Set.Ioi T)).congr_fun (fun t ht => ?_)
      measurableSet_Ioi
    simp [marked_eq_empty d o (le_of_lt (show T < t from ht)), hF]
  exact (h1.union h2).mono_set (fun t ht => by
    by_cases h : t ≤ T
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr (not_le.mp h))

theorem integral_marked_Ioc (F : Set C → ℝ) (hF : F ∅ = 0) :
    ∫ t in Set.Ioi 0, F (marked d o t) = ∫ t in Set.Ioc 0 (maxDistance d o), F (marked d o t) := by
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
  · exact Set.Ioc_subset_Ioi_self
  · intro t ht
    have : maxDistance d o ≤ t := by
      by_contra h
      exact ht.2 ⟨ht.1, (not_le.mp h).le⟩
    simp [marked_eq_empty d o this, hF]

end marks

section tonelli

theorem tonelli_bound (nu : Measure ℝ) [IsFiniteMeasure nu] (a A : ℝ → ℝ)
    (ha : Measurable a) (hA : Measurable A) (r C0 w : ℝ) (hC0 : 0 ≤ C0) (hw : 0 ≤ w) (hr : r ∈ Set.Icc (0:ℝ) 1)
    (hsupp : nu ((Set.Icc (0 : ℝ) 1)ᶜ) = 0) (hmass : nu Set.univ = ENNReal.ofReal C0)
    (hq : ∀ q ∈ Set.Icc (0:ℝ) 1,
      IntegrableOn (fun t => if a t ≤ q ∧ q < A t then (1:ℝ) else 0) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0:ℝ), (if a t ≤ q ∧ q < A t then (1:ℝ) else 0) ≤ w) :
    ∫ t in Set.Ioi (0:ℝ), (nu {z : ℝ | a t ≤ min z r ∧ min z r < A t}).toReal ≤
      C0 * w := by
  set μ0 : Measure ℝ := volume.restrict (Set.Ioi 0) with hμ0
  let fc : ℝ → ℝ → ENNReal := fun t z =>
    ENNReal.ofReal (if a t ≤ min z r ∧ min z r < A t then 1 else 0)
  have hfm : Measurable (Function.uncurry fc) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.ite
    · exact (measurableSet_le (ha.comp measurable_fst) (measurable_snd.min measurable_const)).inter
        (measurableSet_lt (measurable_snd.min measurable_const) (hA.comp measurable_fst))
    · exact measurable_const
    · exact measurable_const
  have hS : ∀ t, MeasurableSet {z : ℝ | a t ≤ min z r ∧ min z r < A t} := by
    intro t
    exact (measurableSet_le measurable_const (measurable_id.min measurable_const)).inter
      (measurableSet_lt (measurable_id.min measurable_const) measurable_const)
  have hfc : ∀ t, ∫⁻ z, fc t z ∂nu = nu {z : ℝ | a t ≤ min z r ∧ min z r < A t} := by
    intro t
    rw [← lintegral_indicator_one (hS t)]
    congr 1; ext z
    simp only [fc, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    split_ifs <;> simp
  have hmeasT : Measurable (fun t => ∫⁻ z, fc t z ∂nu) :=
    hfm.lintegral_prod_right'
  have hconv : ∫ t in Set.Ioi (0:ℝ), (nu {z : ℝ | a t ≤ min z r ∧ min z r < A t}).toReal =
      (∫⁻ t, ∫⁻ z, fc t z ∂nu ∂μ0).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · congr 1
      apply lintegral_congr
      intro t
      rw [hfc t, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    · exact Filter.Eventually.of_forall (fun t => ENNReal.toReal_nonneg)
    · have : (fun t => (nu {z : ℝ | a t ≤ min z r ∧ min z r < A t}).toReal) =
          fun t => (∫⁻ z, fc t z ∂nu).toReal := by
        ext t; rw [hfc t]
      rw [this]
      exact (hmeasT.ennreal_toReal).aestronglyMeasurable
  rw [hconv]
  have hswap : ∫⁻ t, ∫⁻ z, fc t z ∂nu ∂μ0 = ∫⁻ z, ∫⁻ t, fc t z ∂μ0 ∂nu :=
    lintegral_lintegral_swap hfm.aemeasurable
  rw [hswap]
  have hae : ∀ᵐ z ∂nu, z ∈ Set.Icc (0:ℝ) 1 := by
    have := (measure_eq_zero_iff_ae_notMem).mp hsupp
    filter_upwards [this] with z hz
    simpa using hz
  have hle : ∫⁻ z, ∫⁻ t, fc t z ∂μ0 ∂nu ≤ ∫⁻ z, ENNReal.ofReal w ∂nu := by
    apply lintegral_mono_ae
    filter_upwards [hae] with z hz
    have hq' := hq (min z r) ⟨le_min hz.1 hr.1, (min_le_left _ _).trans hz.2⟩
    have : ∫⁻ t, fc t z ∂μ0 =
        ENNReal.ofReal (∫ t in Set.Ioi (0:ℝ), (if a t ≤ min z r ∧ min z r < A t then (1:ℝ) else 0)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hq'.1]
      · exact Filter.Eventually.of_forall (fun t => by
          show (0:ℝ) ≤ _
          dsimp only
          split_ifs <;> simp)
    rw [this]
    exact ENNReal.ofReal_le_ofReal hq'.2
  rw [lintegral_const, hmass] at hle
  have hfin : ENNReal.ofReal w * ENNReal.ofReal C0 ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal] at this
  · linarith
  · exact hC0
  · exact hw

end tonelli

structure Hyps (D : PMF ℕ+) (C₀ b : ℝ) (lam : ℝ → ℝ) (lo hi : Fin 9 → ℝ)
    (nu : Fin 9 → Measure ℝ) (tau : Fin 9 → ℝ → ℝ) : Prop where
  hC : 0 ≤ C₀
  hb : b ∈ Set.Icc (0 : ℝ) 1
  hphi : pgf D b ≤ benchmark D
  hlam : ∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lam p
  hlam0 : lam 0 = 0
  hJ : ∀ j, Set.Icc (lo j) (hi j) ⊆ Set.Icc 0 b
  hcover : ∀ r ∈ Set.Icc (0 : ℝ) b, ∃ j, r ∈ Set.Icc (lo j) (hi j)
  hsupport : ∀ j, nu j ((Set.Icc (0 : ℝ) 1)ᶜ) = 0
  hmass : ∀ j, nu j Set.univ = ENNReal.ofReal C₀
  htau : ∀ j p, p ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ tau j p
  htau0 : ∀ j, tau j 0 = 0
  hcut : ∀ (j : Fin 9) (r : ℝ),
      r ∈ Set.Icc (lo j) (hi j) ∪ Set.Icc b 1 →
      ∀ a p A : ℝ, 0 ≤ a → a ≤ min p r → p ≤ A → A ≤ 1 →
        a + lam p * (primitive D a + primitive D A - primitive D (a + A - p)
          - p * benchmark D) + tau j p * (benchmark D - pgf D r) ≤
        (nu j {z : ℝ | a ≤ min z r ∧ min z r < A}).toReal

section pervoter

variable {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]

theorem marked_not_o (d : V ⊕ C → V ⊕ C → ℝ) (hd : IsPseudometric d) {t : ℝ} (ht : 0 < t)
    (o : C) : o ∉ marked d o t := by
  simp [marked, hd.self, ht.le]

theorem pervoter {D : PMF ℕ+} {C₀ b : ℝ} {lam : ℝ → ℝ} {lo hi : Fin 9 → ℝ}
    {nu : Fin 9 → Measure ℝ} {tau : Fin 9 → ℝ → ℝ}
    (hy : Hyps D C₀ b lam lo hi nu tau)
    (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C)
    (d : V ⊕ C → V ⊕ C → ℝ) (hd : IsPseudometric d) (hc : Consistent E d)
    (o : C) (ho : ∀ c, candCost d o ≤ candCost d c) (v : V) (j : Fin 9)
    (hr : leftRank E P v o ∈ Set.Icc (lo j) (hi j) ∪ Set.Icc b 1) :
    (∫ t in Set.Ioi (0:ℝ), lowerCut E P v (marked d o t)) +
    (∫ t in Set.Ioi (0:ℝ), lam (pm P (marked d o t)) *
      ∫ u in markedRegion E P v (marked d o t), (pgf D u - benchmark D)) +
    (∫ t in Set.Ioi (0:ℝ), tau j (pm P (marked d o t))) *
      (benchmark D - pgf D (leftRank E P v o)) ≤
    2 * C₀ * d (Sum.inl v) (Sum.inr o) := by
  haveI : IsFiniteMeasure (nu j) := ⟨by rw [hy.hmass j]; exact ENNReal.ofReal_lt_top⟩
  set r := leftRank E P v o with hrdef
  have hrb := Common.leftRank_bounds E v o P hP
  have hr01 : r ∈ Set.Icc (0:ℝ) 1 := ⟨hrb.1, by linarith [hrb.2.1, hrb.2.2]⟩
  set μ := benchmark D with hμ
  let Fa : Set C → ℝ := fun S => lowerCut E P v S
  let FI : Set C → ℝ := fun S => lam (pm P S) *
      ∫ u in markedRegion E P v S, (pgf D u - μ)
  let Ft : Set C → ℝ := fun S => tau j (pm P S)
  let Fr : Set C → ℝ := fun S =>
    (nu j {z : ℝ | lowerCut E P v S ≤ min z r ∧ min z r < upperCut E P v S}).toReal
  have hFa : Fa ∅ = 0 := lowerCut_empty E P v
  have hFI : FI ∅ = 0 := by simp [FI, pm_empty, hy.hlam0]
  have hFt : Ft ∅ = 0 := by simp [Ft, pm_empty, hy.htau0]
  have hFr : Fr ∅ = 0 := by
    have : {z : ℝ | lowerCut E P v ∅ ≤ min z r ∧ min z r < upperCut E P v ∅} = ∅ := by
      ext z
      simp only [lowerCut_empty, upperCut_empty, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false]
      intro h; linarith [h.1, h.2]
    show (nu j {z : ℝ | lowerCut E P v ∅ ≤ min z r ∧ min z r < upperCut E P v ∅}).toReal = 0
    rw [this]; simp
  have iFa := integrableOn_marked d o Fa hFa
  have iFI := integrableOn_marked d o FI hFI
  have iFt := integrableOn_marked d o Ft hFt
  have iFr := integrableOn_marked d o Fr hFr
  have hpt : ∀ t : ℝ, 0 < t →
      Fa (marked d o t) + FI (marked d o t) + Ft (marked d o t) * (μ - pgf D r) ≤
        Fr (marked d o t) := by
    intro t ht
    have hoH := marked_not_o d hd ht o
    set S := marked d o t with hS
    have h1 := lowerCut_nonneg E P v hP S
    have h2 : lowerCut E P v S ≤ min (pm P S) r :=
      le_min (lowerCut_le_pm E P v hP S) (lowerCut_le_rank E P v hP S o hoH)
    have h3 := pm_le_upperCut E P v hP S
    have h4 := upperCut_le_one E P v hP S
    have hcutS := hy.hcut j r hr _ _ _ h1 h2 h3 h4
    have hl4 := lemma_4 D (lowerCut E P v S) (pm P S) (upperCut E P v S) h1
      (h2.trans (min_le_left _ _)) h3 h4 (markedRegion E P v S)
      (measurableSet_markedRegion E P v S).nullMeasurableSet
      (markedRegion_subset_Icc E P v hP S) (volume_markedRegion E P v hP S)
      (Ioo_subset_markedRegion E P v hP S)
    have hlam := hy.hlam (pm P S) ⟨pm_nonneg P hP S, pm_le_one P hP S⟩
    have := mul_le_mul_of_nonneg_left hl4 hlam
    simp only [Fa, FI, Ft, Fr]
    linarith
  have hmono : ∫ t in Set.Ioi (0:ℝ), (Fa (marked d o t) + FI (marked d o t) +
      Ft (marked d o t) * (μ - pgf D r)) ≤ ∫ t in Set.Ioi (0:ℝ), Fr (marked d o t) :=
    setIntegral_mono_on ((iFa.add iFI).add (iFt.mul_const _)) iFr measurableSet_Ioi
      (fun t ht => hpt t ht)
  have hlin : ∫ t in Set.Ioi (0:ℝ), (Fa (marked d o t) + FI (marked d o t) +
      Ft (marked d o t) * (μ - pgf D r)) =
      (∫ t in Set.Ioi (0:ℝ), Fa (marked d o t)) + (∫ t in Set.Ioi (0:ℝ), FI (marked d o t)) +
      (∫ t in Set.Ioi (0:ℝ), Ft (marked d o t)) * (μ - pgf D r) := by
    have e1 := integral_add (μ := volume.restrict (Set.Ioi (0:ℝ)))
      (f := fun t => Fa (marked d o t) + FI (marked d o t))
      (g := fun t => Ft (marked d o t) * (μ - pgf D r)) (iFa.add iFI) (iFt.mul_const _)
    have e2 := integral_add (μ := volume.restrict (Set.Ioi (0:ℝ)))
      (f := fun t => Fa (marked d o t)) (g := fun t => FI (marked d o t)) iFa iFI
    have e3 := integral_mul_const (μ := volume.restrict (Set.Ioi (0:ℝ))) (μ - pgf D r)
      (fun t => Ft (marked d o t))
    rw [e1, e2, e3]
  have hd0 : 0 ≤ d (Sum.inl v) (Sum.inr o) := hd.nonneg _ _
  have hT : ∫ t in Set.Ioi (0:ℝ), Fr (marked d o t) ≤ C₀ * (2 * d (Sum.inl v) (Sum.inr o)) := by
    refine tonelli_bound (nu j) (fun t => lowerCut E P v (marked d o t))
      (fun t => upperCut E P v (marked d o t)) (measurable_marked d o _) (measurable_marked d o _)
      r C₀ (2 * d (Sum.inl v) (Sum.inr o)) hy.hC (by linarith) hr01 (hy.hsupport j)
      (hy.hmass j) ?_
    intro q hq
    have := lemma_3 E P hP d hd hc o ho v q hq
    exact ⟨this.2.1, this.2.2.2⟩
  have h5 : (∫ t in Set.Ioi (0:ℝ), Fa (marked d o t)) + (∫ t in Set.Ioi (0:ℝ), FI (marked d o t)) +
      (∫ t in Set.Ioi (0:ℝ), Ft (marked d o t)) * (μ - pgf D r) ≤
      C₀ * (2 * d (Sum.inl v) (Sum.inr o)) := by
    rw [← hlin]; exact hmono.trans hT
  exact le_of_le_of_eq h5 (by ring)

end pervoter

section assembly

variable {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]

noncomputable def Wf (D : PMF ℕ+) (E : Election V C) (P : C → ℝ) (S : Set C) : ℝ :=
  ∑ c, if c ∈ S then P c * (score D E P c - benchmark D) else 0

theorem sum_voters_marked (D : PMF ℕ+) (E : Election V C) (P : C → ℝ)
    (hP : P ∈ stdSimplex ℝ C) (S : Set C) :
    ∑ v, ∫ u in markedRegion E P v S, (pgf D u - benchmark D) =
      (Fintype.card V : ℝ) * Wf D E P S := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := V)).ne'
  simp_rw [integral_marked D E P _ hP S]
  rw [Finset.sum_comm, Wf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : c ∈ S
  · simp only [h, if_true]
    have hsc : score D E P c = (Fintype.card V : ℝ)⁻¹ * ∑ v, comparison D E P v c := rfl
    rw [hsc, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp
  · simp [h]

theorem Wf_univ (D : PMF ℕ+) (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) :
    Wf D E P Set.univ = 0 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := V)).ne'
  have := sum_voters_marked D E P hP Set.univ
  have h0 : ∀ v, ∫ u in markedRegion E P v Set.univ, (pgf D u - benchmark D) = 0 := by
    intro v
    rw [integral_marked D E P v hP]
    simpa using selfplay D E P v hP
  simp only [h0, Finset.sum_const_zero] at this
  exact (mul_eq_zero.mp this.symm).resolve_left hn

theorem pm_add_compl (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (S : Set C) :
    pm P S + pm P Sᶜ = 1 := by
  unfold pm
  rw [← Finset.sum_add_distrib, ← hP.2]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : c ∈ S <;> simp [h]

theorem Wf_lower (D : PMF ℕ+) (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C)
    (δ : ℝ) (hsc : ∀ c, score D E P c ≤ benchmark D + δ) (S : Set C) :
    -(δ * (1 - pm P S)) ≤ Wf D E P S := by
  have h1 : Wf D E P S + Wf D E P Sᶜ = 0 := by
    rw [← Wf_univ D E P hP]
    unfold Wf
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : c ∈ S <;> simp [h]
  have h2 : Wf D E P Sᶜ ≤ δ * pm P Sᶜ := by
    unfold Wf pm
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    split_ifs
    · nlinarith [hP.1 c, hsc c]
    · simp
  have h3 : 1 - pm P S = pm P Sᶜ := by linarith [pm_add_compl P hP S]
  rw [h3]
  linarith

theorem sum_cmp (D : PMF ℕ+) (E : Election V C) (P : C → ℝ) (δ : ℝ)
    (hsc : ∀ c, score D E P c ≤ benchmark D + δ) (o : C) :
    ∑ v, comparison D E P v o ≤ (Fintype.card V : ℝ) * (benchmark D + δ) := by
  have hn : (0:ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos (α := V)
  have h : score D E P o = (Fintype.card V : ℝ)⁻¹ * ∑ v, comparison D E P v o := rfl
  have := hsc o
  rw [h] at this
  rw [inv_mul_le_iff₀ hn] at this
  linarith

theorem core {D : PMF ℕ+} {C₀ b : ℝ} {lam : ℝ → ℝ} {lo hi : Fin 9 → ℝ}
    {nu : Fin 9 → Measure ℝ} {tau : Fin 9 → ℝ → ℝ}
    (hy : Hyps D C₀ b lam lo hi nu tau)
    (E : Election V C) (δ : ℝ) (hδ : 0 ≤ δ) (P : C → ℝ) (hPa : IsApproximatelyStable D E P δ)
    (d : V ⊕ C → V ⊕ C → ℝ) (hd : IsPseudometric d) (hc : Consistent E d)
    (o : C) (ho : ∀ c, candCost d o ≤ candCost d c) :
    ∃ js : Fin 9,
      (∀ j, (∫ t in Set.Ioi (0:ℝ), tau js (pm P (marked d o t))) ≤
        ∫ t in Set.Ioi (0:ℝ), tau j (pm P (marked d o t))) ∧
      lotteryCost d P ≤ (1 + 2 * C₀) * candCost d o +
        δ * ((∫ t in Set.Ioi (0:ℝ), (1 - pm P (marked d o t)) * lam (pm P (marked d o t))) +
          ∫ t in Set.Ioi (0:ℝ), tau js (pm P (marked d o t))) := by
  have hP := hPa.1
  have hsc := hPa.2
  have hn : (0:ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos (α := V)
  obtain ⟨js, -, hjs⟩ := Finset.exists_min_image Finset.univ
    (fun j => ∫ t in Set.Ioi (0:ℝ), tau j (pm P (marked d o t))) Finset.univ_nonempty
  have hKnn : 0 ≤ ∫ t in Set.Ioi (0:ℝ), tau js (pm P (marked d o t)) :=
    setIntegral_nonneg measurableSet_Ioi
      (fun t _ => hy.htau _ _ ⟨pm_nonneg P hP _, pm_le_one P hP _⟩)
  refine ⟨js, fun j => hjs j (Finset.mem_univ _), ?_⟩
  set K := ∫ t in Set.Ioi (0:ℝ), tau js (pm P (marked d o t)) with hK
  set μ := benchmark D with hμ
  -- per voter inequality with the common coefficient
  have hv : ∀ v, (∫ t in Set.Ioi (0:ℝ), lowerCut E P v (marked d o t)) +
      (∫ t in Set.Ioi (0:ℝ), lam (pm P (marked d o t)) *
        ∫ u in markedRegion E P v (marked d o t), (pgf D u - μ)) +
      K * (μ - pgf D (leftRank E P v o)) ≤ 2 * C₀ * d (Sum.inl v) (Sum.inr o) := by
    intro v
    have hrb := Common.leftRank_bounds E v o P hP
    have hr1 : leftRank E P v o ≤ 1 := by linarith [hrb.2.1, hrb.2.2]
    by_cases hlt : leftRank E P v o < b
    · obtain ⟨j, hj⟩ := hy.hcover _ ⟨hrb.1, hlt.le⟩
      have h1 := pervoter hy E P hP d hd hc o ho v j (Or.inl hj)
      have hphi : pgf D (leftRank E P v o) ≤ μ :=
        (pgf_monoOn D ⟨hrb.1, hr1⟩ hy.hb hlt.le).trans hy.hphi
      have h2 := mul_le_mul_of_nonneg_right (hjs j (Finset.mem_univ _)) (sub_nonneg.mpr hphi)
      linarith
    · exact pervoter hy E P hP d hd hc o ho v js (Or.inr ⟨not_lt.mp hlt, hr1⟩)
  set nR : ℝ := (Fintype.card V : ℝ) with hnR
  set J := ∫ t in Set.Ioi (0:ℝ), (1 - pm P (marked d o t)) * lam (pm P (marked d o t)) with hJ
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hv v)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  -- cost identities
  have hLC : nR * lotteryCost d P = ∑ v, ∑ c, P c * d (Sum.inl v) (Sum.inr c) := by
    unfold lotteryCost candCost voterMean
    rw [Finset.mul_sum]
    have : ∀ c, nR * (P c * (nR⁻¹ * ∑ v, d (Sum.inl v) (Sum.inr c))) =
        ∑ v, P c * d (Sum.inl v) (Sum.inr c) := by
      intro c
      rw [← Finset.mul_sum]
      field_simp
    rw [Finset.sum_congr rfl (fun c _ => this c)]
    exact Finset.sum_comm
  have hSC : nR * candCost d o = ∑ v, d (Sum.inl v) (Sum.inr o) := by
    unfold candCost voterMean
    rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  -- (4.1)
  have hα : nR * lotteryCost d P - nR * candCost d o ≤
      ∑ v, ∫ t in Set.Ioi (0:ℝ), lowerCut E P v (marked d o t) := by
    rw [hLC, hSC, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro v _
    have := (lemma_3 E P hP d hd hc o ho v 0 ⟨le_rfl, zero_le_one⟩).2.2.1
    exact this
  -- the mean-zero part
  have hint : ∀ v, IntegrableOn (fun t => lam (pm P (marked d o t)) *
      ∫ u in markedRegion E P v (marked d o t), (pgf D u - μ)) (Set.Ioi 0) := by
    intro v
    exact integrableOn_marked d o (fun S => lam (pm P S) *
      ∫ u in markedRegion E P v S, (pgf D u - μ)) (by simp [pm_empty, hy.hlam0])
  have hG1 := integrableOn_marked d o (fun S => lam (pm P S) * Wf D E P S)
    (by simp [pm_empty, hy.hlam0])
  have hG2 := integrableOn_marked d o (fun S => -δ * ((1 - pm P S) * lam (pm P S)))
    (by simp [pm_empty, hy.hlam0])
  have hβsum : ∑ v, ∫ t in Set.Ioi (0:ℝ), lam (pm P (marked d o t)) *
      ∫ u in markedRegion E P v (marked d o t), (pgf D u - μ) =
      nR * ∫ t in Set.Ioi (0:ℝ), lam (pm P (marked d o t)) * Wf D E P (marked d o t) := by
    rw [← integral_finset_sum _ (fun v _ => hint v), ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    beta_reduce
    have hsvm := sum_voters_marked D E P hP (marked d o t)
    rw [← hμ] at hsvm
    rw [← Finset.mul_sum, hsvm]
    ring
  have hG : -δ * J ≤ ∫ t in Set.Ioi (0:ℝ), lam (pm P (marked d o t)) * Wf D E P (marked d o t) := by
    have h1 : ∫ t in Set.Ioi (0:ℝ), -δ * ((1 - pm P (marked d o t)) * lam (pm P (marked d o t)))
        = -δ * J := integral_const_mul _ _
    rw [← h1]
    apply setIntegral_mono_on hG2 hG1 measurableSet_Ioi
    intro t _
    have hpt : pm P (marked d o t) ∈ Set.Icc (0:ℝ) 1 := ⟨pm_nonneg P hP _, pm_le_one P hP _⟩
    have hl := hy.hlam _ hpt
    have hW := Wf_lower D E P hP δ hsc (marked d o t)
    have := mul_le_mul_of_nonneg_left hW hl
    beta_reduce
    linarith
  -- ϕ(r_v) bound
  have hΦ : ∑ v, pgf D (leftRank E P v o) ≤ nR * (μ + δ) :=
    (Finset.sum_le_sum (fun v _ => pgf_le_comparison D E P v hP o)).trans (sum_cmp D E P δ hsc o)
  have hKΦ := mul_le_mul_of_nonneg_left
    (show ∑ v, pgf D (leftRank E P v o) - nR * μ ≤ nR * δ by linarith) hKnn
  rw [← hSC] at hsum
  have hB := mul_le_mul_of_nonneg_left hG hn.le
  rw [← hβsum] at hB
  have hmain : nR * lotteryCost d P ≤ nR * ((1 + 2 * C₀) * candCost d o + δ * (J + K)) := by
    nlinarith
  exact le_of_mul_le_mul_left hmain hn

end assembly

end RandomSizeStable.Dev.L5

namespace RandomSizeStable

/-- Lemma 5, p.13: the nine-measure rank-cut criterion and its full
approximate-stability clause. Witnesses are hypotheses here, never in the goal. -/
theorem chk_lemma_5 (D : PMF ℕ+) (C₀ b : ℝ) (hC : 0 ≤ C₀)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hphi : pgf D b ≤ benchmark D)
    (lam : ℝ → ℝ) (hlam : ∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lam p)
    (hlam0 : lam 0 = 0) (hlam1 : lam 1 = 0)
    (lo hi : Fin 9 → ℝ)
    (hJ : ∀ j, Set.Icc (lo j) (hi j) ⊆ Set.Icc 0 b)
    (hcover : ∀ r ∈ Set.Icc (0 : ℝ) b, ∃ j, r ∈ Set.Icc (lo j) (hi j))
    (nu : Fin 9 → Measure ℝ)
    (hsupport : ∀ j, nu j ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hmass : ∀ j, nu j Set.univ = ENNReal.ofReal C₀)
    (tau : Fin 9 → ℝ → ℝ)
    (htau : ∀ j p, p ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ tau j p)
    (htau0 : ∀ j, tau j 0 = 0)
    (hcut : ∀ (j : Fin 9) (r : ℝ),
      r ∈ Set.Icc (lo j) (hi j) ∪ Set.Icc b 1 →
      ∀ a p A : ℝ, 0 ≤ a → a ≤ min p r → p ≤ A → A ≤ 1 →
        a + lam p * (primitive D a + primitive D A - primitive D (a + A - p)
          - p * benchmark D) + tau j p * (benchmark D - pgf D r) ≤
        (nu j {z : ℝ | a ≤ min z r ∧ min z r < A}).toReal) :
    ∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
      (E : Election V C),
      (∀ P : C → ℝ, IsStable D E P → HasDistortionAtMost E P (1 + 2 * C₀)) ∧
      (∀ B : ℝ, (∀ p ∈ Set.Icc (0 : ℝ) 1, (1 - p) * lam p + tau 0 p ≤ B) →
        ∀ (δ : ℝ), 0 ≤ δ → ∀ P : C → ℝ, IsApproximatelyStable D E P δ →
        ∀ d : V ⊕ C → V ⊕ C → ℝ, IsPseudometric d → Consistent E d →
        ∀ o : C, (∀ c, candCost d o ≤ candCost d c) →
          lotteryCost d P ≤ (1 + 2 * C₀) * candCost d o + B * δ * maxDistance d o) := by
  intro V C _ _ _ _ E
  have hy : Dev.L5.Hyps D C₀ b lam lo hi nu tau :=
    ⟨hC, hb, hphi, hlam, hlam0, hJ, hcover, hsupport, hmass, htau, htau0, hcut⟩
  refine ⟨?_, ?_⟩
  · intro P hs d hd hc a
    obtain ⟨o, -, ho⟩ := Finset.exists_min_image Finset.univ (fun c => candCost d c)
      Finset.univ_nonempty
    have hPa : IsApproximatelyStable D E P 0 := ⟨hs.1, fun c => by simpa using hs.2 c⟩
    obtain ⟨js, -, h⟩ := Dev.L5.core hy E 0 le_rfl P hPa d hd hc o
      (fun c => ho c (Finset.mem_univ c))
    have h1 := ho a (Finset.mem_univ a)
    simp only [zero_mul, add_zero] at h
    have h2 : (0:ℝ) ≤ 1 + 2 * C₀ := by linarith
    nlinarith
  · intro B hB δ hδ P hPa d hd hc o ho
    obtain ⟨js, hjs, h⟩ := Dev.L5.core hy E δ hδ P hPa d hd hc o ho
    have hpt : ∀ S : Set C, Dev.L5.pm P S ∈ Set.Icc (0:ℝ) 1 := fun S =>
      ⟨Dev.L5.pm_nonneg P hPa.1 S, Dev.L5.pm_le_one P hPa.1 S⟩
    have iJ := Dev.L5.integrableOn_marked d o (fun S => (1 - Dev.L5.pm P S) * lam (Dev.L5.pm P S))
      (by simp [Dev.L5.pm_empty, hlam0])
    have iK := Dev.L5.integrableOn_marked d o (fun S => tau 0 (Dev.L5.pm P S))
      (by simp [Dev.L5.pm_empty, htau0])
    have hT0 : 0 ≤ maxDistance d o :=
      le_trans (hd.nonneg _ _) (Finset.le_sup' (fun c => d (Sum.inr o) (Sum.inr c))
        (Finset.mem_univ o))
    have hsumint : (∫ t in Set.Ioi (0:ℝ), (1 - Dev.L5.pm P (marked d o t)) * lam (Dev.L5.pm P (marked d o t))) +
        ∫ t in Set.Ioi (0:ℝ), tau 0 (Dev.L5.pm P (marked d o t)) =
        ∫ t in Set.Ioc (0:ℝ) (maxDistance d o),
          ((1 - Dev.L5.pm P (marked d o t)) * lam (Dev.L5.pm P (marked d o t)) +
            tau 0 (Dev.L5.pm P (marked d o t))) := by
      rw [← integral_add iJ iK]
      exact Dev.L5.integral_marked_Ioc d o (fun S => (1 - Dev.L5.pm P S) * lam (Dev.L5.pm P S) +
        tau 0 (Dev.L5.pm P S)) (by simp [Dev.L5.pm_empty, hlam0, htau0])
    have hbound : ∫ t in Set.Ioc (0:ℝ) (maxDistance d o),
          ((1 - Dev.L5.pm P (marked d o t)) * lam (Dev.L5.pm P (marked d o t)) +
            tau 0 (Dev.L5.pm P (marked d o t))) ≤ B * maxDistance d o := by
      have hc' : ∫ t in Set.Ioc (0:ℝ) (maxDistance d o), B = B * maxDistance d o := by
        rw [setIntegral_const]
        simp [Measure.real, hT0, mul_comm]
      rw [← hc']
      apply setIntegral_mono_on
      · exact (iJ.add iK).mono_set Set.Ioc_subset_Ioi_self
      · exact integrableOn_const (by simp)
      · exact measurableSet_Ioc
      · intro t _
        exact hB _ (hpt _)
    have hK := hjs 0
    nlinarith
end RandomSizeStable
end

theorem solution : type_of% @RandomSizeStable.chk_lemma_5 := @RandomSizeStable.chk_lemma_5

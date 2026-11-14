-- Prove2me | solution 1 for avram_chat24_mapped_jump_cell_integral_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:15:28.229952+00:00
-- url     : https://prove2.me/submissions/d10a5897-15e2-45fd-b16f-afa5171203bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution
    (Δ : ℝ≥0 → ℝ) (hΔ : Measurable Δ)
    (hdown : ∀ r : ℝ≥0, 0 < r → Δ r ≤ 0)
    (s t : ℝ≥0)
    (hsum : Summable (fun r : ℝ≥0 => if s < r ∧ r ≤ t then -Δ r else 0)) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ Δ r ≠ 0}).map
        (fun r : ℝ≥0 => (r, Δ r)))
    let H : ℝ≥0 × ℝ → ℝ := fun p => if s < p.1 ∧ p.1 ≤ t then -p.2 else 0
    Integrable H NX ∧ (∫ p, H p ∂NX) =
      ∑' r : ℝ≥0, if s < r ∧ r ≤ t then -Δ r else 0 := by
  classical
  let S : Set ℝ≥0 := {r | 0 < r ∧ Δ r ≠ 0}
  let τ : ℝ≥0 → ℝ≥0 × ℝ := fun r => (r, Δ r)
  let g : ℝ≥0 → ℝ := fun r => if s < r ∧ r ≤ t then -Δ r else 0
  let H : ℝ≥0 × ℝ → ℝ := fun p => if s < p.1 ∧ p.1 ≤ t then -p.2 else 0
  change Integrable H ((Measure.count.restrict S).map τ) ∧
    (∫ p, H p ∂((Measure.count.restrict S).map τ)) = ∑' r, g r
  have hS : MeasurableSet S :=
    measurableSet_Ioi.inter (hΔ (measurableSet_singleton 0)).compl
  have hτ : Measurable τ := measurable_id.prodMk hΔ
  have hH : Measurable H := by
    exact measurable_snd.neg.piecewise
      (measurableSet_Ioc.preimage measurable_fst) measurable_const
  have hc : Integrable g Measure.count := integrable_count_iff.2 hsum.norm
  have hi : Integrable g (Measure.count.restrict S) :=
    hc.mono_measure Measure.restrict_le_self
  have hm : Integrable H ((Measure.count.restrict S).map τ) :=
    (integrable_map_measure hH.aestronglyMeasurable hτ.aemeasurable).2 hi
  have hind : S.indicator g = g := by
    funext r
    by_cases hr : r ∈ S
    · simp [Set.indicator, hr]
    · have hz : g r = 0 := by
        by_cases hcell : s < r ∧ r ≤ t
        · have hp : 0 < r := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hcell.1
          have hd0 : Δ r = 0 := by
            by_contra hd0
            exact hr ⟨hp, hd0⟩
          simp [g, hd0]
        · simp [g, hcell]
      simp [Set.indicator, hr, hz]
  refine ⟨hm, ?_⟩
  rw [integral_map hτ.aemeasurable hH.aestronglyMeasurable]
  change (∫ r, g r ∂(Measure.count.restrict S)) = ∑' r, g r
  rw [← integral_indicator hS, hind]
  simpa only [Measure.count, integral_dirac] using
    (integral_sum_measure (μ := fun r : ℝ≥0 => Measure.dirac r) hc)

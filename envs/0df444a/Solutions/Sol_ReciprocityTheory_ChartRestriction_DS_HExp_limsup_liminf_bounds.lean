-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.limsup_liminf_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:09:56.646292+00:00
-- url     : https://prove2.me/submissions/ae4176e1-cf8d-4884-aa87-49546c256d26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_tendsto_mul_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]
namespace ReciprocityTheory.ChartRestriction.DS.HExp
theorem _root_.solution {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hq : QInv nu ε δ) :
    ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      limsup (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤
        ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * L ∧
      ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * L ≤
        liminf (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
  have hae := (Besicovitch.ae_tendsto_rnDeriv nu lam).and (Measure.rnDeriv_lt_top nu lam)
  obtain ⟨X, hXm, hX, hXfin⟩ : ∃ X ∈ ball (0 : V) δ,
      Tendsto (fun r => nu (closedBall X r) / lam (closedBall X r)) (𝓝[>] 0) (𝓝 (nu.rnDeriv lam X)) ∧
        nu.rnDeriv lam X < ⊤ := by
    by_contra hcon
    push Not at hcon
    have hsub : ball (0 : V) δ ⊆ {X | ¬ (Tendsto (fun r => nu (closedBall X r) / lam (closedBall X r))
        (𝓝[>] 0) (𝓝 (nu.rnDeriv lam X)) ∧ nu.rnDeriv lam X < ⊤)} := by
      intro X hX h
      exact absurd h.2 (not_lt.mpr (hcon X hX h.1))
    have h0 := measure_mono_null hsub (ae_iff.mp hae)
    exact (measure_ball_pos lam (0 : V) hδ).ne' h0
  have hXn : ‖X‖ < δ := by simpa using hXm
  refine ⟨nu.rnDeriv lam X, hXfin.ne, ?_, ?_⟩
  · have hA0 : ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hg : Tendsto (fun r : ℝ => ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) *
        (nu (closedBall X ((1 + ε) * r)) / lam (closedBall X ((1 + ε) * r)))) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
      ENNReal.Tendsto.const_mul (hX.comp (tendsto_mul_pos (by linarith)))
        (Or.inr ENNReal.ofReal_ne_top)
    rw [← hg.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    rw [Measure.addHaar_closedBall_mul_of_pos lam X (by linarith) r, ← mul_div_assoc,
      ENNReal.mul_div_mul_left _ _ hA0 ENNReal.ofReal_ne_top]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).2 _
  · have hB0 : ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      have : 0 < 1 - ε := by linarith
      positivity
    have hg : Tendsto (fun r : ℝ => ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) *
        (nu (closedBall X ((1 - ε) * r)) / lam (closedBall X ((1 - ε) * r)))) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
      ENNReal.Tendsto.const_mul (hX.comp (tendsto_mul_pos (by linarith)))
        (Or.inr ENNReal.ofReal_ne_top)
    rw [← hg.liminf_eq]
    refine liminf_le_liminf ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    rw [Measure.addHaar_closedBall_mul_of_pos lam X (by linarith) r, ← mul_div_assoc,
      ENNReal.mul_div_mul_left _ _ hB0 ENNReal.ofReal_ne_top]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).1 _
end ReciprocityTheory.ChartRestriction.DS.HExp

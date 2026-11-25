-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.integrable_tsum_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:05:54.989259+00:00
-- url     : https://prove2.me/submissions/f44c966c-5294-4836-b9ca-8be5846195fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Set Filter Topology Function
variable {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} (hF : ∀ n, Integrable (F n) μ) (hs : Summable fun n => ∫ y, ‖F n y‖ ∂μ) :
    Integrable (fun y => ∑' n, F n y) μ := by
  have hmeas : ∀ n, AEMeasurable (fun y => ‖F n y‖ₑ) μ := fun n => (hF n).aemeasurable.enorm
  have hlin : ∫⁻ y, ∑' n, ‖F n y‖ₑ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have : ∀ n, ∫⁻ y, ‖F n y‖ₑ ∂μ = ENNReal.ofReal (∫ y, ‖F n y‖ ∂μ) := fun n =>
      (ofReal_integral_norm_eq_lintegral_enorm (hF n)).symm
    simp_rw [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun _ => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ y ∂μ, ∑' n, ‖F n y‖ₑ < ⊤ := ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hlin
  have hsum : ∀ᵐ y ∂μ, Summable fun n => F n y := by
    filter_upwards [hae] with y hy
    refine Summable.of_norm ?_
    have : (∑' n, (‖F n y‖₊ : ENNReal)) ≠ ⊤ := hy.ne
    exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp this)
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ n ∈ Finset.range N, F n y)
    (fun N => Finset.aestronglyMeasurable_fun_sum _ fun n _ => (hF n).1) ?_, ?_⟩
  · filter_upwards [hsum] with y hy
    exact hy.hasSum.tendsto_sum_nat
  · refine lt_of_le_of_lt (lintegral_mono fun y => enorm_tsum_le_tsum_enorm) ?_
    exact lt_top_iff_ne_top.mpr hlin
end ReciprocityTheory.ChartRestriction.G.Geo

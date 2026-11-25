-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.measurable_mul_complexLineSecondDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:38:34.199579+00:00
-- url     : https://prove2.me/submissions/bbbc67d8-fbef-4b22-b4c4-ff63caa3d8a3

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_hasDerivAt_realLine_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) (e : V n) {χ : V n → ℂ} (hχ : Measurable χ)
    (hχΩ : ∀ z, χ z ≠ 0 → z ∈ Ω) : Measurable (fun z => χ z * complexLineSecondDeriv F z e) := by

  have hΦ : Measurable (fun w => fderiv ℂ F w e) := measurable_fderiv_apply_const ℂ F e
  have hu0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => Set.mem_compl_singleton_iff.2 (by positivity)⟩
  refine measurable_of_tendsto_metrizable
    (f := fun (k : ℕ) z => χ z * ((1 / ((k : ℝ) + 1))⁻¹ •
      (fderiv ℂ F (z + (1 / ((k : ℝ) + 1)) • ((1 : ℂ) • e)) e - fderiv ℂ F z e)))
    (fun k => ?_) (tendsto_pi_nhds.2 fun z => ?_)
  · refine hχ.mul ?_
    have hm := ((hΦ.comp (measurable_add_const ((1 / ((k : ℝ) + 1)) • ((1 : ℂ) • e)))).sub hΦ).const_smul
      ((1 / ((k : ℝ) + 1))⁻¹)
    exact hm
  · by_cases hz : χ z = 0
    · simp only [hz, zero_mul]
      exact tendsto_const_nhds
    · have hd := hasDerivAt_realLine_fderiv hΩ hF (hχΩ z hz) e 1
      have hs := (hd.tendsto_slope_zero.comp hu0).const_mul (χ z)
      simpa using hs
end ReciprocityTheory.L2DbarEstimates.C

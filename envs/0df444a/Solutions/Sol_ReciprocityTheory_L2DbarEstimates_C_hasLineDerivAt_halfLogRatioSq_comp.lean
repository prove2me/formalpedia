-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.hasLineDerivAt_halfLogRatioSq_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:17.167799+00:00
-- url     : https://prove2.me/submissions/81e46103-a824-49cf-ac86-c1f4cac78faa

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_hasDerivAt_cutP


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
    (hF : DifferentiableOn ℂ F Ω) {z : V n} (hz : z ∈ Ω) {ε : ℝ} (hε : 0 < ε) (e : V n)
    (μ : ℂ) :
    HasLineDerivAt ℝ (fun w => cutP ε (‖F w‖ ^ 2)) (lineFirstVariation ε (F z) (fderiv ℂ F z e * μ)) z
      (μ • e) := by
  have hs : 0 < ‖F z‖ ^ 2 + ε := by positivity
  have hFd : HasFDerivAt F (fderiv ℂ F z) z :=
    (hF.differentiableAt (hΩ.mem_nhds hz)).hasFDerivAt
  have hFR := hFd.restrictScalars ℝ
  have hN := hFR.norm_sq
  have hC := (hasDerivAt_cutP hs).comp_hasFDerivAt z hN
  have hL := hC.hasLineDerivAt (μ • e)
  refine HasDerivAt.congr_deriv hL ?_
  simp only [lineFirstVariation, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply, map_smul, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring
end ReciprocityTheory.L2DbarEstimates.C

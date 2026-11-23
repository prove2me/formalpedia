-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.fderiv_logCutoff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:10.759536+00:00
-- url     : https://prove2.me/submissions/bdcc6360-8d2a-412f-8468-305a3c6b4720

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_extCh_contDiff

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
open scoped ENNReal ContDiff
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {F : V n → ℂ} {k : ℝ} {z : V n}
    (hF : DifferentiableAt ℝ F z) (hz : F z ≠ 0) :
    fderiv ℝ (extCut F k) z = deriv extCh (-Real.log (‖F z‖ ^ 2) / k) •
      ((-k⁻¹) • fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z) := by
  have hne : ‖F z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hz)
  have hL : HasFDerivAt (fun w => Real.log (‖F w‖ ^ 2))
      (fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z) z :=
    (((hF.norm_sq ℝ).log hne)).hasFDerivAt
  have e : (fun w => -Real.log (‖F w‖ ^ 2) / k) =
      fun w => (-k⁻¹) • Real.log (‖F w‖ ^ 2) := by
    funext w
    simp only [smul_eq_mul]
    ring
  have hh : HasFDerivAt (fun w => -Real.log (‖F w‖ ^ 2) / k)
      ((-k⁻¹) • fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z) z := by
    rw [e]
    exact hL.const_smul (-k⁻¹ : ℝ)
  have hd : HasDerivAt extCh (deriv extCh (-Real.log (‖F z‖ ^ 2) / k))
      (-Real.log (‖F z‖ ^ 2) / k) :=
    ((extCh_contDiff.differentiable (by simp)) _).hasDerivAt
  have hcomp := hd.comp_hasFDerivAt z hh
  have heq : extCut F k =ᶠ[𝓝 z] extCh ∘ fun w => -Real.log (‖F w‖ ^ 2) / k := by
    filter_upwards [hF.continuousAt.eventually_ne hz] with w hw
    simp [extCut, hw]
  rw [heq.fderiv_eq]
  exact hcomp.fderiv
end ReciprocityTheory.L2DbarEstimates.C

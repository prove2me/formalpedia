-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.pgds_discI_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:26:27.617317+00:00
-- url     : https://prove2.me/submissions/d8b94a2b-8a24-4fa2-b990-09a731ec0077

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgds_integral_ball_polar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Filter Topology
open Set
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    discI a R = ∫ s in (0:ℝ)..R, 2 * Real.pi * (s * Real.exp (-(a * s ^ 2))) := by
  unfold discI
  rw [(pgds_integral_ball_polar (r := R) (fun z : ℂ => Real.exp (-(a * ‖z‖ ^ 2)))
    (by fun_prop)).2, intervalIntegral.integral_of_le hR, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)
  simp only [Complex.norm_polarCoord_symm]
  rw [abs_of_pos hs.1, setIntegral_const]
  simp only [measureReal_def, Real.volume_Ioo, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring
end ReciprocityTheory.GeometryOfNumbersTheory

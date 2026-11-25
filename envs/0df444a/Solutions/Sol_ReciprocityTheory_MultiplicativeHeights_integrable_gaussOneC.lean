-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integrable_gaussOneC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:20:22.243869+00:00
-- url     : https://prove2.me/submissions/dad2cd2d-57b6-4e40-8732-9f56e199f022

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real
private theorem integrableOn_rpow_mul_exp_neg_sq_Ioi (s : ℝ) (hs : -1 < s) :
    IntegrableOn (fun y : ℝ ↦ y ^ s * exp (-1 * y ^ 2)) (Ioi 0) :=
  integrableOn_rpow_mul_exp_neg_mul_sq one_pos hs
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : Integrable (fun z : ℂ ↦ exp (-‖z‖ ^ 2)) := by
  refine (integrable_fun_norm_addHaar volume (f := fun y : ℝ ↦ exp (-y ^ 2))).mpr ?_
  have hd : Module.finrank ℝ ℂ - 1 = 1 := by simp [Complex.finrank_real_complex]
  simp only [hd, pow_one, smul_eq_mul]
  refine (integrableOn_rpow_mul_exp_neg_sq_Ioi 1 (by norm_num)).congr_fun
    (fun y _ ↦ by simp [Real.rpow_one]) measurableSet_Ioi
end ReciprocityTheory.MultiplicativeHeights

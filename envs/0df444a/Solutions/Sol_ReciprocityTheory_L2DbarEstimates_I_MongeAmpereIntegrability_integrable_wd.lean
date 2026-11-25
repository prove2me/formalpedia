-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.integrable_wd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:14:49.660066+00:00
-- url     : https://prove2.me/submissions/a4c7c0b3-3c25-44e4-8901-06fad29fd14a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_IntegrableWd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_wd_zero_of_eqOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
noncomputable section
open ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
theorem _root_.solution {H : V n → ℂ} (hH : ContDiff ℝ 1 H) (hc : HasCompactSupport H)
    (j : Fin n) : Integrable (wd n j H) := by
  have h1 : Continuous fun y => fderiv ℝ H y (bas n j) :=
    (hH.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h2 : Continuous fun y => fderiv ℝ H y (Complex.I • bas n j) :=
    (hH.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcont : Continuous (wd n j H) := (h1.sub (continuous_const.mul h2)).div_const 2
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hc.isCompact fun y hy => ?_)
  exact (wd_zero_of_eqOn (isClosed_tsupport H).isOpen_compl
    (fun w hw => image_eq_zero_of_notMem_tsupport hw) j hy).1
end ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability

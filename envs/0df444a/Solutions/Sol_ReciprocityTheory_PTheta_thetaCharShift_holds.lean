-- Prove2me | solution 1 for ReciprocityTheory.PTheta.thetaCharShift_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:13:45.22049+00:00
-- url     : https://prove2.me/submissions/0fd8f96d-cd03-4890-b39c-9463e294ef37

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add
import Theorems.Thm_ReciprocityTheory_PTheta_eC_zero
import Theorems.Thm_ReciprocityTheory_PTheta_thetaRealTransl_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta
theorem _root_.solution : ThetaCharShiftStatement := by
  intro ι _ a b a' b' z τ hτ
  rw [thetaRealTransl_holds ι a' b' a b z τ hτ, ← mul_assoc, ← eC_add]
  convert (one_mul (theta (a' + a) (b' + b) z τ)).symm using 2
  rw [← eC_zero]
  congr 1
  simp only [dotProduct_add]
  ring
end ReciprocityTheory.PTheta

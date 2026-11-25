-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_antisym_permTerm_76dab284b23e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:52.086459+00:00
-- url     : https://prove2.me/submissions/6ada48bc-b8fc-4188-8517-5534b52dcebf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_alternant_eq_sum_27b6851fc1aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_antisym_eq_sum_314cba1d0338
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_rename_permTerm_ef56a29d8e15
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_permSign_mul__3be578588ef6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_permSign_inv__c2e72e289cc8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.KAlt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.KAlt
theorem _root_.solution (e : ι → ℕ) (π : Equiv.Perm ι) :
    antisym (permTerm e π) = sgnP π * alternant e := by
  rw [antisym_eq_sum, alternant_eq_sum, mul_sum]
  simp_rw [rename_permTerm]
  refine (Equiv.sum_comp (Equiv.mulRight π⁻¹) _).symm.trans ?_
  refine sum_congr rfl fun u _ => ?_
  simp only [Equiv.coe_mulRight, inv_mul_cancel_right, permSign_mul₂, permSign_inv₂]
  ring
end GroundTheory.Heights₂.Heights.KAlt

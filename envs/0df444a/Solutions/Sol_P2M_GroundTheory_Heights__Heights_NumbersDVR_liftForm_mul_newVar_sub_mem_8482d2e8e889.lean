-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mul_newVar_sub_mem_8482d2e8e889
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:39.074927+00:00
-- url     : https://prove2.me/submissions/8d9df650-6dc0-4adc-aaf9-b50e2687d3f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpLocalChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_newVar_7a8cf0aa599e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_liftForm_4b99591f2332


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (P : Ideal (MRing ι R)) (u : J → MRing ι R) (j k : J) :
    liftForm (u j) * newVar k - liftForm (u k) * newVar j ∈ blowUpOf P u := by
  rw [blowUpOf, RingHom.mem_ker, map_sub, map_mul, map_mul, aeval_blowUpSubst_liftForm,
    aeval_blowUpSubst_liftForm, aeval_blowUpSubst_newVar, aeval_blowUpSubst_newVar]
  ring
end GroundTheory.Heights₂.Heights.NumbersDVR

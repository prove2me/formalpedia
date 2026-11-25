-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_inh_restTerm_b831e71f17f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:46:31.184804+00:00
-- url     : https://prove2.me/submissions/68f5292f-163b-4c5a-bb0b-f38f4114940e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_second_root_eb297a48e2f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_C_mul_e0cd3fab3f15
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_smallPowerSum_one_3d745d2237e4

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (τ τ' : Fin 1) :
    restTerm 1 (1 + 1) inhQ 2 τ (smallPowerSum 1 1 1 .last (2 - 1) τ') = -1 := by
  have hQ : inhQ 2 τ = C (2⁻¹) := by simp [inhQ]
  rw [show (2 : ℕ) - 1 = 1 from rfl, inh_smallPowerSum_one, restTerm, hQ, mul_comm flagTwoSecondRoot,
    flagIntegral_C_mul, flagIntegral_second_root]
  norm_num
end GroundTheory.Heights₂.Heights.RestTerms

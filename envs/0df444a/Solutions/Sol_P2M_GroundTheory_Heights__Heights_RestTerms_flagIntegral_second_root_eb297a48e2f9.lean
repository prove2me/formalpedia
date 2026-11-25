-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_second_root_eb297a48e2f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:50.322896+00:00
-- url     : https://prove2.me/submissions/cc0cb299-d72b-404a-b680-8f1a08088ed9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_J_eq_083d9017b1ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_fib_eq_3eb15ec2cff6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_mu_eq_f35e2c531be1


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
theorem _root_.solution : flagIntegral 1 (1 + 1) flagTwoSecondRoot = -1 := by
  have h := inh_J_eq
  have hH : smallBlockMu 1 1 1 .last ^ (1 * (1 * 1)) * fibreClass 1 1 1 .last = flagTwoSecondRoot := by
    simp [inh_mu_eq, inh_fib_eq]
  rwa [fibreDegree, hH] at h
end GroundTheory.Heights₂.Heights.RestTerms

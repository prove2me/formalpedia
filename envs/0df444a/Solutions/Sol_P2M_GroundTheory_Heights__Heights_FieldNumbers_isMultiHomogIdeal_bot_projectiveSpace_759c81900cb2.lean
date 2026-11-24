-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_bot_projectiveSpace_759c81900cb2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:22.990753+00:00
-- url     : https://prove2.me/submissions/a5a36174-34e7-494f-bf5d-e3381fcc73f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiProjPrime_bot_dfd17cf75014


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (N : ℕ) :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx N) ℚ)) :=
  isMultiProjPrime_bot.multiHomog
end GroundTheory.Heights₂.Heights.FieldNumbers

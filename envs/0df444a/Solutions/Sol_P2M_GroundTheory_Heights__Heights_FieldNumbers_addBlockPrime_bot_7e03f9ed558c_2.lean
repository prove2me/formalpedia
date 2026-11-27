-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_FieldNumbers_addBlockPrime_bot_7e03f9ed558c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:55:00.291381+00:00
-- url     : https://prove2.me/submissions/05b4f2ad-f65a-4ea2-bd86-19dd3f071bac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples

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
theorem _root_.solution {K : Type*} {F : Type*} [Field F] (ι : K → Type) (N : ℕ) :
    addBlockPrime N (⊥ : Ideal (MRing ι F)) = ⊥ :=
  Ideal.map_bot
end GroundTheory.Heights₂.Heights.FieldNumbers

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_lt_withBotWithTop_6ec59031adae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:11:12.462577+00:00
-- url     : https://prove2.me/submissions/79dc0cb3-d8d4-461a-8cdd-f1fdcb3ccba3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameHilbFn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRelevantPrimeDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_BlockInclInjectiveOfEmbedding

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
namespace PFContracted
theorem _root_.solution {a b : ℕ} (h : a < b) :
    ((a : ℕ) : WithBot (WithTop ℤ)) < ((b : ℕ) : WithBot (WithTop ℤ)) := by
  show (((a : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < (((b : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by exact_mod_cast h))
end PFContracted
end GroundTheory.Heights₂.Heights.FieldNumbers

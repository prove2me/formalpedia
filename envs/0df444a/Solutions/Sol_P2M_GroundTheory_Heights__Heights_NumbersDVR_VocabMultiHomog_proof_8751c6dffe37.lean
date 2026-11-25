-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabMultiHomog_proof_8751c6dffe37
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:58.550397+00:00
-- url     : https://prove2.me/submissions/c6b835d1-36f3-4ba9-8478-a7cd70aae993

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_blockWeight_apply_6df27136a502

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
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace VocabMultiHomog
theorem _root_.solution : VocabMultiHomog.Statement := by
  intro R _ K _ _ ι _ s a
  constructor
  · intro h d hd
    funext k
    rw [weight_blockWeight_apply]
    exact h d (MvPolynomial.mem_support_iff.mpr hd) k
  · intro h m hm k
    rw [← weight_blockWeight_apply]
    exact congrFun (h (MvPolynomial.mem_support_iff.mp hm)) k
end VocabMultiHomog
end GroundTheory.Heights₂.Heights.NumbersDVR

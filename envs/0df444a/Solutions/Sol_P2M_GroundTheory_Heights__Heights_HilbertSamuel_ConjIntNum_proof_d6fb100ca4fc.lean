-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_proof_d6fb100ca4fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:06.99472+00:00
-- url     : https://prove2.me/submissions/fa5721c2-9882-4e76-8efb-2307b8f2c20a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConjIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConjIntNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_hilbFn_map_8078c1f8a395

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
theorem _root_.solution : ConjIntNum.Statement := by
  intro K _ ι F _ τ J n bs
  unfold NumbersDVR.intNum
  rw [hilbFn_map]
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum

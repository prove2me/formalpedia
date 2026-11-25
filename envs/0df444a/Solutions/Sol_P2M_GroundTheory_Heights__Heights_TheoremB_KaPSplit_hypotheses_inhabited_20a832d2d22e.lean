-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_KaPSplit_hypotheses_inhabited_20a832d2d22e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:29.618179+00:00
-- url     : https://prove2.me/submissions/be3f0dbb-981b-4220-bc0f-3d70706d8a89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_StatementsEnd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_isFrobLike_one_f2b818bede79

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset Filter Topology
variable (d : IndexData)
variable {d}
namespace GroundTheory.Heights₂.Heights.TheoremB
namespace KaPSplit
theorem _root_.solution : Nat.Prime 2 ∧ IsFrobLike d1 1 ∧ IsSplitFrob d1 1 :=
  ⟨Nat.prime_two, isFrobLike_one d1, fun _ => rfl⟩
end KaPSplit
end GroundTheory.Heights₂.Heights.TheoremB

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_NefAtBaseHeight_hypotheses_inhabited_022ed8d4e067
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:58.403103+00:00
-- url     : https://prove2.me/submissions/479a6acf-21c8-4f57-8ec0-a40a0847632b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_StatementsEnd

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
namespace NefAtBaseHeight
theorem _root_.solution : 0 < d1.f ∧ (0 : ℝ) < 1 := ⟨Nat.one_pos, one_pos⟩
end NefAtBaseHeight
end GroundTheory.Heights₂.Heights.TheoremB

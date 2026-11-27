-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_ShTotIndependent_hypotheses_inhabited_c82c05800523
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:09:12.817124+00:00
-- url     : https://prove2.me/submissions/dcde98ad-bc47-4da8-9e8e-0ddc8c4f77ab

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
namespace ShTotIndependent
theorem _root_.solution : 0 < d1.f := Nat.one_pos
end ShTotIndependent
end GroundTheory.Heights₂.Heights.TheoremB

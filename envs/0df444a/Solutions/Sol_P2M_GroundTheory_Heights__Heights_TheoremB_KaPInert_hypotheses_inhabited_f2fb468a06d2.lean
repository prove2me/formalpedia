-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_KaPInert_hypotheses_inhabited_f2fb468a06d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:23.759336+00:00
-- url     : https://prove2.me/submissions/b2bc2748-abf4-4956-a9ed-3e412b3ebcef

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
namespace KaPInert
theorem _root_.solution :
    Nat.Prime 2 ∧ IsFrobLike d1 (conjPerm d1) ∧ IsInertFrob d1 (conjPerm d1) :=
  ⟨Nat.prime_two, ⟨fun _ => rfl, Or.inr fun _ => rfl⟩, fun _ => rfl⟩
end KaPInert
end GroundTheory.Heights₂.Heights.TheoremB

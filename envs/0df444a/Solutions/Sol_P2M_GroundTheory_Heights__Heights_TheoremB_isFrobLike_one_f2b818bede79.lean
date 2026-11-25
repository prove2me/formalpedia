-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_isFrobLike_one_f2b818bede79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:22:10.662751+00:00
-- url     : https://prove2.me/submissions/0757e921-0793-4f49-a354-b970f697d827

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
theorem _root_.solution (d : IndexData) : IsFrobLike d 1 :=
  ⟨fun _ => rfl, Or.inl fun _ => rfl⟩
end GroundTheory.Heights₂.Heights.TheoremB

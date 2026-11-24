-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestBound_proof_0d78e9e9eb76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:08:33.29738+00:00
-- url     : https://prove2.me/submissions/ea0e388c-a008-4d66-8fff-6f65aaf95cdd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace RestBound
theorem _root_.solution (h₁ : RestPrimeBound.Statement) (h₂ : RestBoundOfPrimeBound.Statement) :
    RestBound.Statement := by
  intro f r a c B₀ hf hr ha hB
  refine ⟨(h₁ f r a c B₀ hf hr ha hB).1, ?_⟩
  intro Q hQ s e he P
  exact h₂ f r a c B₀ hf hr ha hB Q s e
    (fun p hp hpB => (h₁ f r a c B₀ hf hr ha hB).2 Q hQ s e he p hp hpB) P
end RestBound
end GroundTheory.Heights₂.Heights.RestTerms

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CycleSectionData_proof_a7b247e9b6ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:55.327451+00:00
-- url     : https://prove2.me/submissions/0cfa1068-b353-4dab-ba00-4a4354099dc2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PCycleSectionData

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
namespace GroundTheory.Heights₂.Heights
namespace CycleSectionData
theorem _root_.solution (h1 : CycleSectionChow.Statement) (h2 : DivCyclePrime.Statement)
    (h3 : SpecFirstHomog.Statement) (h4 : SupportCycleSection.Statement) :
    CycleSectionData.Statement := by
  intro n e δ Z f u hZ hu
  refine ⟨?_, ?_, ?_⟩
  · intro W' hW'
    obtain ⟨W, hW, hW'W⟩ := (h4 n Z u).2 W' hW'
    exact h2 n W u (hZ.prime W hW) W' hW'W
  · exact h1 n (e + 1) Z f u hZ.prime hZ.chow hu
  · exact h3 n (e + 1) δ f u hZ.homog
end CycleSectionData
end GroundTheory.Heights₂.Heights

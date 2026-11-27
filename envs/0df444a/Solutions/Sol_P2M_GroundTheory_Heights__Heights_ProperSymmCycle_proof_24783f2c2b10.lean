-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProperSymmCycle_proof_24783f2c2b10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:08:00.17808+00:00
-- url     : https://prove2.me/submissions/29201a24-762c-4e06-b41e-1f93cb6a0a72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymmCycle

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
namespace ProperSymmCycle
theorem _root_.solution (h1 : ProperSymm.Statement) (h2 : SupportCycleSection.Statement) :
    ProperSymmCycle.Statement := by
  intro n Z u u' hprime hu hu' hadm W'' hW''
  obtain ⟨W, hW, hW''W⟩ := (h2 n Z u').2 W'' hW''
  have hadmW : IsAdmissible (divCycle W u) u' := fun W' hW' =>
    hadm W' ((h2 n Z u).1 W hW hW')
  exact h1 n W u u' (hprime W hW) (hu W hW) (hu' W hW) hadmW W'' hW''W
end ProperSymmCycle
end GroundTheory.Heights₂.Heights

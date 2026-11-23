-- Prove2me | solution 1 for P2M_Csg_idsCSG_stageGame_A__7bb1bc444f1d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:55:05.084448+00:00
-- url     : https://prove2.me/submissions/c93ab67e-57cf-4b84-a7c5-79065605de6d

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_idsCSG_expect

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction)
    (v : IDSState → ℝ) :
    (idsCSG.stageGame s v).A a1 a2 = idsR s a1 a2 + v (idsNext a1 a2) := by
  have hexpect : idsCSG.expect s a1 a2 v = v (idsNext a1 a2) := idsCSG_expect s a1 a2 v
  change idsCSG.r s a1 a2 + idsCSG.expect s a1 a2 v = idsR s a1 a2 + v (idsNext a1 a2)
  rw [hexpect]
  rfl
end Csg

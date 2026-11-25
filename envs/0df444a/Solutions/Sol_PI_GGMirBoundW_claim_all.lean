-- Prove2me | solution 1 for PI.GGMirBoundW.claim_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:43.585386+00:00
-- url     : https://prove2.me/submissions/674f7d70-88d4-4b6f-8819-c83b8b402525

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGMirBoundW
open Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
namespace PI.GGMirBoundW
theorem _root_.solution (hb : BaseProp) (hs : StepProp) (F : Type) [Field F] [Fintype F] : ∀ n, Claim F n := by
  intro n
  induction n with
  | zero => exact hb F
  | succ n ih => exact hs F n ih
end PI.GGMirBoundW

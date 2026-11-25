-- Prove2me | solution 1 for PI.AmpRootCommon.det_unitri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:02.972213+00:00
-- url     : https://prove2.me/submissions/1c79d759-3429-4551-b446-1df9cfa9e3b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.AmpRootCommon
variable {n : ℕ}
namespace PI.AmpRootCommon
theorem _root_.solution {u : Matrix (Fin n) (Fin n) ℂ} (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) :
    u.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular hu]; simp [hud]
end PI.AmpRootCommon

-- Prove2me | solution 1 for PI.AmpRootCommon.isUnit_unitri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:20:17.129533+00:00
-- url     : https://prove2.me/submissions/eca044e3-2803-4b28-8c2d-d64946210e42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
import Theorems.Thm_PI_AmpRootCommon_det_unitri

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
    IsUnit u.det := by
  rw [det_unitri hu hud]; exact isUnit_one
end PI.AmpRootCommon

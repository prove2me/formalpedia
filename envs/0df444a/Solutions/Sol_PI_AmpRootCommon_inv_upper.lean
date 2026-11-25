-- Prove2me | solution 1 for PI.AmpRootCommon.inv_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:06.145903+00:00
-- url     : https://prove2.me/submissions/61bd72dd-f985-4400-a78e-e6c29cdc7a64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
import Theorems.Thm_PI_AmpRootCommon_isUnit_unitri

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
    u⁻¹.BlockTriangular id := by
  have : Invertible u := Matrix.invertibleOfIsUnitDet u (isUnit_unitri hu hud)
  exact Matrix.blockTriangular_inv_of_blockTriangular hu
end PI.AmpRootCommon

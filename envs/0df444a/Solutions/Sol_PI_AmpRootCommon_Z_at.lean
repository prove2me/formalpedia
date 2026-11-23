-- Prove2me | solution 1 for PI.AmpRootCommon.Z_at
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:46.60398+00:00
-- url     : https://prove2.me/submissions/e81c4010-2a21-49e0-9b20-23dc6b60ac50

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
variable {Z u u' : Matrix (Fin n) (Fin n) ℂ} {σ : Fin n → Fin n} {ζ : Fin n → ℂ}
namespace PI.AmpRootCommon
theorem _root_.solution (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (i : Fin n) : Z i (σ i) = ζ i := by
  rw [hZ, if_pos rfl]
end PI.AmpRootCommon

-- Prove2me | solution 1 for P2M_PI_AmpRootCommon_Z_at__9514a3b6830f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:12.066865+00:00
-- url     : https://prove2.me/submissions/aaba4901-935e-4e64-8a8a-5d03cd25e007

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
theorem _root_.solution (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (j : Fin n) :
    Z (σ j) j = ζ (σ j) := by
  rw [hZ, if_pos (hσ j).symm]
end PI.AmpRootCommon

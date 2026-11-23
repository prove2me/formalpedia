-- Prove2me | solution 1 for PI.AmpRootCommon.Z_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:47.611381+00:00
-- url     : https://prove2.me/submissions/810a89aa-66c4-4365-87e1-9785963c0c69

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
theorem _root_.solution (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (i b : Fin n) (hb : b ≠ σ i) : Z i b = 0 := by
  rw [hZ, if_neg hb]
end PI.AmpRootCommon

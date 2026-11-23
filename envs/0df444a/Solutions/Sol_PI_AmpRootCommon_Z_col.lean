-- Prove2me | solution 1 for PI.AmpRootCommon.Z_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:46.695135+00:00
-- url     : https://prove2.me/submissions/ee3430ea-7d4b-45f7-955e-bbb7eaa05ce8

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
theorem _root_.solution (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (a j : Fin n)
    (ha : a ≠ σ j) : Z a j = 0 := by
  rw [hZ, if_neg]; intro e; apply ha; rw [e, hσ]
end PI.AmpRootCommon

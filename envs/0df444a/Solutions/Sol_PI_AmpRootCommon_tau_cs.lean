-- Prove2me | solution 1 for PI.AmpRootCommon.tau_cs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:48.024802+00:00
-- url     : https://prove2.me/submissions/e3b81985-a964-451e-a1e2-23ff49ab1449

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
import Theorems.Thm_PI_AmpRootCommon_tau_val

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
variable {m : ℕ}
namespace PI.AmpRootCommon
theorem _root_.solution {σ : Fin (m + 1) → Fin (m + 1)} {i : Fin m} (h : (σ i.succ).val + 1 = (σ i.castSucc).val) :
    (tau σ i).castSucc = σ i.succ := by
  apply Fin.ext; rw [Fin.val_castSucc, tau_val h]
end PI.AmpRootCommon

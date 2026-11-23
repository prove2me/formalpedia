-- Prove2me | solution 1 for PI.AmpRootCommon.tau_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:15.052498+00:00
-- url     : https://prove2.me/submissions/65374340-2969-41af-b552-1ebbb240cdc0

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
    (tau σ i).succ = σ i.castSucc := by
  apply Fin.ext; rw [Fin.val_succ, tau_val h, h]
end PI.AmpRootCommon

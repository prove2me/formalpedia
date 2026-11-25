-- Prove2me | solution 1 for PI.AmpRootCommon.tau_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:33.727578+00:00
-- url     : https://prove2.me/submissions/a3d2a814-b202-43e2-a5c5-57384a7ef83e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
import Theorems.Thm_PI_AmpRootCommon_tau_val
import Theorems.Thm_PI_AmpRootCommon_tau_neg
import Theorems.Thm_PI_AmpRootCommon_tau_succ
import Theorems.Thm_PI_AmpRootCommon_superdiagPairing_adjacent

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
theorem _root_.solution {σ : Fin (m + 1) → Fin (m + 1)} (hσ : ∀ i, σ (σ i) = i) : Function.Involutive (tau σ) := by
  intro i
  by_cases h : (σ i.succ).val + 1 = (σ i.castSucc).val
  · apply Fin.ext
    rw [tau_val (superdiagPairing_adjacent hσ h), tau_succ h, hσ, Fin.val_castSucc]
  · rw [tau_neg h, tau_neg h]
end PI.AmpRootCommon

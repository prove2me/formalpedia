-- Prove2me | solution 1 for PI.AmpRootCommon.superdiagPairing_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:07.804606+00:00
-- url     : https://prove2.me/submissions/c71931e8-7ae1-4ebe-89f3-f119beeea18f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
import Theorems.Thm_PI_AmpRootCommon_tau_cs
import Theorems.Thm_PI_AmpRootCommon_tau_succ

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
theorem _root_.solution {σ : Fin (m + 1) → Fin (m + 1)} (hσ : ∀ i, σ (σ i) = i) {i : Fin m}
    (h : (σ i.succ).val + 1 = (σ i.castSucc).val) :
    (σ (tau σ i).succ).val + 1 = (σ (tau σ i).castSucc).val := by
  rw [tau_succ h, tau_cs h, hσ, hσ, Fin.val_castSucc, Fin.val_succ]
end PI.AmpRootCommon

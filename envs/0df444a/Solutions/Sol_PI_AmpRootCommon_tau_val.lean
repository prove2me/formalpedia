-- Prove2me | solution 1 for PI.AmpRootCommon.tau_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:55:37.41765+00:00
-- url     : https://prove2.me/submissions/54533d20-fa41-43ea-8c6b-a5d35671cd33

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
variable {m : ℕ}
namespace PI.AmpRootCommon
theorem _root_.solution {σ : Fin (m + 1) → Fin (m + 1)} {i : Fin m} (h : (σ i.succ).val + 1 = (σ i.castSucc).val) :
    (tau σ i).val = (σ i.succ).val := by
  simp [tau, h]
end PI.AmpRootCommon

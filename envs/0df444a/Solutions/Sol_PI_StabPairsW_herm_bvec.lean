-- Prove2me | solution 1 for PI.StabPairsW.herm_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:33:26.874841+00:00
-- url     : https://prove2.me/submissions/1c1eda14-807a-4f46-b852-71e97bdf4362

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV

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
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) v (bvec j) = (Hpk k r *ᵥ v) j := by
  simp [herm, bvec, dotProduct, Pi.single_apply]
end PI.StabPairsW

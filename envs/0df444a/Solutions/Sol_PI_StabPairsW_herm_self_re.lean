-- Prove2me | solution 1 for PI.StabPairsW.herm_self_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:28:00.226662+00:00
-- url     : https://prove2.me/submissions/273b861e-9612-4fcb-9fa7-5b22b1653af5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_herm_swap

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
theorem _root_.solution (v : Fin (2 * r + k + 1) → ℂ) :
    ((herm (Hpk k r) v v).re : ℂ) = herm (Hpk k r) v v := by
  have h := herm_swap (k := k) (r := r) v v
  exact Complex.conj_eq_iff_re.1 h.symm
end PI.StabPairsW

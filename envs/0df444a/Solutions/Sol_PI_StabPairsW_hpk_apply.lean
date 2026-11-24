-- Prove2me | solution 1 for PI.StabPairsW.hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:33:28.945796+00:00
-- url     : https://prove2.me/submissions/813cdfc8-d044-4234-8483-a01a5d47a14a

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
theorem _root_.solution (i l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if l.val = sgI k r i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hl := l.isLt
  simp only [Hpk, sgI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)
end PI.StabPairsW

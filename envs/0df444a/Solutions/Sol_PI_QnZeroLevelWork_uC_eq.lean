-- Prove2me | solution 1 for PI.QnZeroLevelWork.uC_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:11:55.427346+00:00
-- url     : https://prove2.me/submissions/812102b2-8bbf-447a-afb9-65fe93573078

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnZeroLevelWork
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ}
namespace PI.QnZeroLevelWork
theorem _root_.solution (k r : ℕ) (Y : ℂ) :
    uC (k + 1) r 0 Y = Y + (((2 * r + (k + 1) + 1 : ℕ) : ℂ) / 2 - 1 / 2) := by
  simp only [uC, mdim, Fin.val_zero, Nat.sub_zero]
  push_cast
  ring
end PI.QnZeroLevelWork

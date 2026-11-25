-- Prove2me | solution 1 for PI.QnZeroLevelWork.comp2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:18:29.884715+00:00
-- url     : https://prove2.me/submissions/9a0a50ea-ef3e-44bf-beaa-762e3596fe81

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula
import Theorems.Thm_PI_QnZeroLevelWork_skip_two_succAbove_comp_alt

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
theorem _root_.solution (i : Fin (2 * r + k + 2)) (i'' : Fin (2 * r + k + 1)) (h : (i : ℕ) ≤ (i'' : ℕ)) :
    (posL (k + 1) r 0 ∘ skip2 i (i.succAbove i'') : Fin (2 * r + k + 2 - 2) → Fin (2 * r + (k + 1) + 1)) =
      drop2 i i'' := by
  funext j
  exact skip_two_succAbove_comp_alt i i'' j h
end PI.QnZeroLevelWork

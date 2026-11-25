-- Prove2me | solution 1 for PI.QnZeroLevelWork.second_minor_zero_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:36.614158+00:00
-- url     : https://prove2.me/submissions/8ba9e65e-5c9f-4b5e-8fcc-780cbcf26f6d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula
import Theorems.Thm_PI_QnZeroLevelWork_second_minor_zero_level_formula

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
theorem _root_.solution (u : ℂ) (a a' β β' : Mx (k + 1) r → Fin (mdim (k + 1) r 0) → ℂ) (f : Mx (k + 1) r → E) :
    chat2L (EH (k + 1) r) (posL (k + 1) r 0) u a a' β β' f =
      chat2Op (m := 2 * r + k) (EabH (Hpk (k + 1) r)) u a a' β β' f :=
  second_minor_zero_level_formula u a a' β β' f
end PI.QnZeroLevelWork

-- Prove2me | solution 1 for PI.QnRT.w_col_other
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:04:50.343803+00:00
-- url     : https://prove2.me/submissions/21bcaabd-88e7-42f2-9be7-2df282d88d9c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}
namespace PI.QnRT
theorem _root_.solution (l : Fin r) (a : ℂ) (s p : Fin (2 * r + k + 1)) (hp1 : p ≠ eI k r l)
    (hp2 : p ≠ esI k r l) : w1 k r l a s p = if s = p then 1 else 0 := by
  unfold w1
  by_cases h : s = p
  · subst h
    simp [hp1, hp2]
  · simp [h, hp1, hp2]
end PI.QnRT

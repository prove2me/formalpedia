-- Prove2me | solution 1 for PI.QnRT.w_row_other
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:07.806106+00:00
-- url     : https://prove2.me/submissions/6f2544c2-c1ac-4c12-a086-2703881e5f25

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
theorem _root_.solution (l : Fin r) (a : ℂ) (s q : Fin (2 * r + k + 1)) (hs1 : s ≠ eI k r l)
    (hs2 : s ≠ esI k r l) : w1 k r l a s q = if s = q then 1 else 0 := by
  unfold w1
  by_cases h : s = q
  · subst h
    simp [hs1, hs2]
  · simp [h, hs1, hs2]
end PI.QnRT

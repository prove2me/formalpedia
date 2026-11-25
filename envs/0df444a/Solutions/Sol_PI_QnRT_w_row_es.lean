-- Prove2me | solution 1 for PI.QnRT.w_row_es
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:18:26.8588+00:00
-- url     : https://prove2.me/submissions/73950569-6c4c-4b19-95e9-82baf444767b

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Theorems.Thm_PI_QnRT_e_ne_es

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
theorem _root_.solution (l : Fin r) (a : ℂ) (q : Fin (2 * r + k + 1)) :
    w1 k r l a (esI k r l) q = if q = eI k r l then a else 0 := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold w1
  by_cases h : q = eI k r l
  · subst h
    simp [hne, hne.symm]
  · simp [h, hne, hne.symm]
end PI.QnRT

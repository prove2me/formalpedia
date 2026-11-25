-- Prove2me | solution 1 for PI.QnRT.w_row_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:11:43.456908+00:00
-- url     : https://prove2.me/submissions/a3e6801e-bd1e-4038-9d33-e16814a242b1

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
    w1 k r l a (eI k r l) q = if q = esI k r l then (star a)⁻¹ else 0 := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold w1
  by_cases h : q = esI k r l
  · subst h
    simp [hne, hne.symm]
  · simp [h, hne, hne.symm]
end PI.QnRT

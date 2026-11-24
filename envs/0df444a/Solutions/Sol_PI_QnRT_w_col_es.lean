-- Prove2me | solution 1 for PI.QnRT.w_col_es
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:48:28.22065+00:00
-- url     : https://prove2.me/submissions/4862a525-c301-4ecc-af26-8e0eeff2afcb

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
theorem _root_.solution (l : Fin r) (a : ℂ) (s : Fin (2 * r + k + 1)) :
    w1 k r l a s (esI k r l) = if s = eI k r l then (star a)⁻¹ else 0 := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold w1
  by_cases h : s = eI k r l
  · subst h
    simp [hne, hne.symm]
  · simp [h, hne, hne.symm]
end PI.QnRT

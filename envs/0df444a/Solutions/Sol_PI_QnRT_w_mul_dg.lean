-- Prove2me | solution 1 for PI.QnRT.w_mul_dg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:11:38.823985+00:00
-- url     : https://prove2.me/submissions/ac54c06e-1905-41b3-b32b-72db6496e984

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Theorems.Thm_PI_QnRT_e_ne_es
import Theorems.Thm_PI_QnRT_w_col_e
import Theorems.Thm_PI_QnRT_w_col_es
import Theorems.Thm_PI_QnRT_w_col_other

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
theorem _root_.solution (l : Fin r) (a u : ℂ) :
    w1 k r l a * dg l u (star u)⁻¹ = w1 k r l (a * u) := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold dg
  ext p q
  rw [Matrix.mul_diagonal]
  by_cases hq1 : q = eI k r l
  · subst hq1
    rw [w_col_e, w_col_e]
    by_cases hp : p = esI k r l <;> simp [hp]
  by_cases hq2 : q = esI k r l
  · subst hq2
    rw [w_col_es, w_col_es]
    by_cases hp : p = eI k r l <;> simp [hp, hne.symm, mul_inv, mul_comm]
  rw [w_col_other l a p q hq1 hq2, w_col_other l (a * u) p q hq1 hq2]
  simp [hq1, hq2]
end PI.QnRT

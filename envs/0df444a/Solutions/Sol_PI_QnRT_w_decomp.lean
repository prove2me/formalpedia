-- Prove2me | solution 1 for PI.QnRT.w_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:11:26.680357+00:00
-- url     : https://prove2.me/submissions/d918a6ca-0bb3-4999-be34-2fccb6d171b6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
import Theorems.Thm_PI_QnRT_e_ne_es


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}
namespace PI.QnRT
theorem _root_.solution (l : Fin r) (b : ℂ) :
    w1 k r l b = w1 k r l 0 + b • single (esI k r l) (eI k r l) 1 +
      (star b)⁻¹ • single (eI k r l) (esI k r l) 1 := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  unfold w1
  by_cases hp1 : p = eI k r l
  · subst hp1
    by_cases hq2 : q = esI k r l
    · subst hq2
      simp [hne, hne.symm]
    · simp [hne, hne.symm, hq2, Ne.symm hq2]
  · by_cases hp2 : p = esI k r l
    · subst hp2
      by_cases hq1 : q = eI k r l
      · subst hq1
        simp [hne, hne.symm]
      · simp [hne, hne.symm, hq1, Ne.symm hq1]
    · simp [hp1, hp2, Ne.symm hp1, Ne.symm hp2]
end PI.QnRT

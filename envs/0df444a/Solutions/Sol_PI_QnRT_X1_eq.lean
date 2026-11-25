-- Prove2me | solution 1 for PI.QnRT.X1_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:03.517771+00:00
-- url     : https://prove2.me/submissions/47b64ae2-0af6-432b-829d-09ee3b9686f2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
import Theorems.Thm_PI_QnRT_inv_conj_single
import Theorems.Thm_PI_QnRT_e_ne_es
import Theorems.Thm_PI_QnRT_tau_e


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
theorem _root_.solution (l : Fin r) : hpart1 (Hpk k r) (single (eI k r l) (eI k r l) 1) =
    dz l ((1 / 2 : ℝ) : ℂ) (-((1 / 2 : ℝ) : ℂ)) := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold hpart1 dz
  rw [inv_conj_single, tau_e]
  ext p q
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq
    by_cases h1 : p = eI k r l
    · subst h1
      simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
    · by_cases h2 : p = esI k r l
      · subst h2
        simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · have a1 : ¬ (eI k r l = p ∧ eI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    have a2 : ¬ (esI k r l = p ∧ esI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    simp [a1, a2, hpq]
end PI.QnRT

-- Prove2me | solution 1 for PI.QnWCellW.reflection_mul_weyl_cell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:10:31.22914+00:00
-- url     : https://prove2.me/submissions/6c7a70d2-2e21-482e-824a-852e725caa0c

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell
import Theorems.Thm_PI_QnWCellW_cN_val
import Theorems.Thm_PI_QnWCellW_weyl_cell_mul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.QnWCellW.cN_val

set_option autoImplicit false
open Matrix Finset
open PI PI.QnWCellW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
set_option maxHeartbeats 800000
namespace PI.QnWCellW
theorem _root_.solution (k r : ℕ) (S : Finset ℕ) (c : Fin r → ℂ) (a : Fin r) (ha : a.val ∉ S) :
    w1 k r a (c a) * Wm k r S c = Wm k r (insert a.val S) c := by
  ext p q
  rw [weyl_cell_mul_apply]
  have hA := a.isLt
  have hp := p.isLt
  have hq := q.isLt
  have vE : (eI k r a).val = a.val := rfl
  have vS : (esI k r a).val = 2 * r + k - a.val := rfl
  simp only [Wm, Finset.mem_insert]
  by_cases h1 : q.val = a.val
  · simp only [h1, ha, eq_self_iff_true, true_or, or_false, if_true, if_false]
    split_ifs <;> (try simp only [Fin.ext_iff, vE, vS] at *) <;> first | rfl | (exfalso; omega) | (simp; done) | (simp_all; done)
  · by_cases h2 : q.val = 2 * r + k - a.val
    · have e2 : 2 * r + k - (2 * r + k - a.val) = a.val := by omega
      simp only [h2, e2, ha, eq_self_iff_true, true_or, or_false, if_true, if_false]
      split_ifs <;> (try simp only [Fin.ext_iff, vE, vS] at *) <;> first | rfl | (exfalso; omega) | (simp; done) | (simp_all; done)
    · have h3 : 2 * r + k - q.val ≠ a.val := by omega
      simp only [h1, h3, false_or]
      split_ifs <;> (try simp only [Fin.ext_iff, vE, vS] at *) <;> first | rfl | (exfalso; omega) | (simp; done) | (simp_all; done)
end PI.QnWCellW

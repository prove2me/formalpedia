-- Prove2me | solution 1 for PI.QnWCellW.weyl_cell_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:07:06.295172+00:00
-- url     : https://prove2.me/submissions/225e9b4e-64a6-4f54-963e-a2b5f2a23989

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell
import Theorems.Thm_PI_QnWCellW_cN_val
import Theorems.Thm_PI_QnWCellW_eI_ne_esI
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
namespace PI.QnWCellW
theorem _root_.solution (k r : ℕ) (l : Fin r) (d : ℂ) (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (w1 k r l d * M) p q =
      if p = esI k r l then d * M (eI k r l) q
      else if p = eI k r l then (star d)⁻¹ * M (esI k r l) q else M p q := by
  have hne := eI_ne_esI k r l
  rw [Matrix.mul_apply]
  by_cases h1 : p = esI k r l
  · subst h1
    rw [if_pos rfl, Finset.sum_eq_single (eI k r l)]
    · simp [w1]
    · intro x _ hx
      simp [w1, hx, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · by_cases h2 : p = eI k r l
    · subst h2
      rw [if_neg h1, if_pos rfl, Finset.sum_eq_single (esI k r l)]
      · simp [w1, hne]
      · intro x _ hx
        simp [w1, hx, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg h1, if_neg h2, Finset.sum_eq_single p]
      · simp [w1, h1, h2]
      · intro x _ hx
        simp [w1, h1, h2, Ne.symm hx]
      · intro h; exact absurd (Finset.mem_univ _) h
end PI.QnWCellW

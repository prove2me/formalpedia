-- Prove2me | solution 1 for PI.IsotropicReflections.w1_commute_of_mem_Glev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:02:41.444286+00:00
-- url     : https://prove2.me/submissions/0572befc-9263-40e4-bd37-a7f3f9a23473

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic
import Theorems.Thm_PI_IsotropicReflections_eI_ne_esI
import Theorems.Thm_PI_IsotropicReflections_sw_e
import Theorems.Thm_PI_IsotropicReflections_swap_dual_isotropic
import Theorems.Thm_PI_IsotropicReflections_sw_o
import Theorems.Thm_PI_IsotropicReflections_al_e
import Theorems.Thm_PI_IsotropicReflections_reflection_scalar_dual_isotropic
import Theorems.Thm_PI_IsotropicReflections_al_o
import Theorems.Thm_PI_IsotropicReflections_trich
import Theorems.Thm_PI_IsotropicReflections_weyl_lift_eq_pair
import Theorems.Thm_PI_IsotropicReflections_reflection_row_formula
import Theorems.Thm_PI_IsotropicReflections_g_col_e
import Theorems.Thm_PI_IsotropicReflections_diagonal_column_dual_isotropic
import Theorems.Thm_PI_IsotropicReflections_diagonal_row_dual_isotropic
import Theorems.Thm_PI_IsotropicReflections_g_row_e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.IsotropicReflections
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {k r : ℕ}
variable (l : Fin r) (g : Mx k r) (hg : g ∈ Glev k r l.succ)
include hg
namespace PI.IsotropicReflections
theorem _root_.solution (c : ℂ) : w1 k r l c * g = g * w1 k r l c := by
  ext p q
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp_rw [reflection_row_formula l c p, (weyl_lift_eq_pair l c · q)]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hr1 := g_row_e l g hg
  have hr2 := diagonal_row_dual_isotropic l g hg
  have hc1 := g_col_e l g hg
  have hc2 := diagonal_column_dual_isotropic l g hg
  rcases trich l p with hp | hp | ⟨hp1, hp2⟩ <;> rcases trich l q with hq | hq | ⟨hq1, hq2⟩ <;>
    (try subst hp) <;> (try subst hq) <;>
    simp [sw_e, swap_dual_isotropic, al_e, reflection_scalar_dual_isotropic, sw_o, al_o, eI_ne_esI, (eI_ne_esI l).symm, *]
end PI.IsotropicReflections

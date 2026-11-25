-- Prove2me | solution 1 for PI.IsotropicReflections.reflection_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:09:53.81249+00:00
-- url     : https://prove2.me/submissions/2dfba8bd-2822-438a-921e-94347140834f

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
import Theorems.Thm_PI_IsotropicReflections_hpk_e_row
import Theorems.Thm_PI_IsotropicReflections_hpk_s_row
import Theorems.Thm_PI_IsotropicReflections_hpk_e_col
import Theorems.Thm_PI_IsotropicReflections_hpk_s_col
import Theorems.Thm_PI_IsotropicReflections_monomial_conj

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
namespace PI.IsotropicReflections
theorem _root_.solution (l : Fin r) (c : ℂ) (hc : c ≠ 0) : w1 k r l c ∈ UH (Hpk k r) := by
  simp only [UH, Set.mem_setOf_eq]
  ext p q
  rw [monomial_conj _ _ (sw l) (al l c) (weyl_lift_eq_pair l c)]
  rcases trich l p with hp | hp | ⟨hp1, hp2⟩ <;> rcases trich l q with hq | hq | ⟨hq1, hq2⟩ <;>
    (try subst hp) <;> (try subst hq) <;>
    simp [sw_e, swap_dual_isotropic, al_e, reflection_scalar_dual_isotropic, sw_o, al_o, hpk_e_row, hpk_s_row, hpk_e_col, hpk_s_col, eI_ne_esI,
      (eI_ne_esI l).symm, hc, *]
end PI.IsotropicReflections

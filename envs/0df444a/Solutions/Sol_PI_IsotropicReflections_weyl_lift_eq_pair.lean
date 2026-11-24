-- Prove2me | solution 1 for PI.IsotropicReflections.weyl_lift_eq_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:03:19.333926+00:00
-- url     : https://prove2.me/submissions/a8647bbb-d49b-4d0f-9d21-d09a421a531f

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
theorem _root_.solution (l : Fin r) (c : ℂ) (i q : Fin (2 * r + k + 1)) :
    w1 k r l c i q = if i = sw l q then al l c q else 0 := by
  rcases trich l q with hq | hq | ⟨hq1, hq2⟩ <;> rcases trich l i with hi | hi | ⟨hi1, hi2⟩ <;>
    (try subst hq) <;> (try subst hi) <;> (try have hq1' := Ne.symm hq1) <;> (try have hq2' := Ne.symm hq2) <;>
    (try have hi1' := Ne.symm hi1) <;> (try have hi2' := Ne.symm hi2) <;>
    simp [w1, sw_e, swap_dual_isotropic, al_e, reflection_scalar_dual_isotropic, sw_o, al_o, eI_ne_esI, (eI_ne_esI l).symm, *]
end PI.IsotropicReflections

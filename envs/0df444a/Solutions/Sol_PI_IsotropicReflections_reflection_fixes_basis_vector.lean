-- Prove2me | solution 1 for PI.IsotropicReflections.reflection_fixes_basis_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:14:49.136102+00:00
-- url     : https://prove2.me/submissions/247d94e0-eb3f-4c9c-aa3b-94850aeb0b93

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic
import Theorems.Thm_PI_IsotropicReflections_sw_o
import Theorems.Thm_PI_IsotropicReflections_al_o
import Theorems.Thm_PI_IsotropicReflections_weyl_lift_eq_pair
import Theorems.Thm_PI_IsotropicReflections_mulVec_bvec

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
theorem _root_.solution (l : Fin r) (c : ℂ) (j : Fin (2 * r + k + 1)) (h1 : j ≠ eI k r l) (h2 : j ≠ esI k r l) :
    w1 k r l c *ᵥ bvec j = bvec j := by
  rw [mulVec_bvec]
  funext i
  rw [weyl_lift_eq_pair, sw_o l h1 h2, al_o l c h1 h2]
  simp [bvec, Pi.single_apply]
end PI.IsotropicReflections

-- Prove2me | solution 1 for PI.IsotropicReflections.reflection_row_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:44:06.611812+00:00
-- url     : https://prove2.me/submissions/db49ba6c-4cf0-49ae-aca5-9258f6187b1b

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic
import Theorems.Thm_PI_IsotropicReflections_sw_sw
import Theorems.Thm_PI_IsotropicReflections_weyl_lift_eq_pair

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
theorem _root_.solution (l : Fin r) (c : ℂ) (p i : Fin (2 * r + k + 1)) :
    w1 k r l c p i = if i = sw l p then al l c (sw l p) else 0 := by
  rw [weyl_lift_eq_pair]
  by_cases h : i = sw l p
  · subst h
    rw [sw_sw]
    simp
  · have h' : p ≠ sw l i := fun h' => h (by rw [h', sw_sw])
    simp [h, h']
end PI.IsotropicReflections

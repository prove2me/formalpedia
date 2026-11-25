-- Prove2me | solution 1 for PI.IsotropicReflections.sw_sw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:15:56.580501+00:00
-- url     : https://prove2.me/submissions/306d68f6-e336-490b-b3f3-6dbdbb499b5d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic
import Theorems.Thm_PI_IsotropicReflections_sw_e
import Theorems.Thm_PI_IsotropicReflections_swap_dual_isotropic
import Theorems.Thm_PI_IsotropicReflections_sw_o
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
theorem _root_.solution (l : Fin r) (p : Fin (2 * r + k + 1)) : sw l (sw l p) = p := by
  rcases trich l p with h | h | ⟨h1, h2⟩
  · subst h
    rw [sw_e, swap_dual_isotropic]
  · subst h
    rw [swap_dual_isotropic, sw_e]
  · rw [sw_o l h1 h2, sw_o l h1 h2]
end PI.IsotropicReflections

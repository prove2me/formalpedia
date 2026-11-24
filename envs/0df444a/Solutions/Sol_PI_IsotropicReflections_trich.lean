-- Prove2me | solution 1 for PI.IsotropicReflections.trich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:56:51.446599+00:00
-- url     : https://prove2.me/submissions/aed37b14-1c8f-434e-aab6-6573b180f782

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic

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
theorem _root_.solution (l : Fin r) (p : Fin (2 * r + k + 1)) :
    p = eI k r l ∨ p = esI k r l ∨ (p ≠ eI k r l ∧ p ≠ esI k r l) := by
  by_cases h1 : p = eI k r l
  · exact Or.inl h1
  · by_cases h2 : p = esI k r l
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
end PI.IsotropicReflections

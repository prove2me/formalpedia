-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.eN_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:24:18.770777+00:00
-- url     : https://prove2.me/submissions/46bfd554-af59-4b03-9ddc-ae6efde47e7b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CoreW
namespace PI.PolynomialProperness.CoreW
theorem _root_.solution {n : ℕ} (x y : Fin n → ℂ) : eN (x - y) ≤ eN x + eN y := by
  simp only [eN, WithLp.toLp_sub]
  exact norm_sub_le _ _
end PI.PolynomialProperness.CoreW

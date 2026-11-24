-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.nsq_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:42:27.383834+00:00
-- url     : https://prove2.me/submissions/67f52c7c-0e34-44e1-8d85-02407a2406d6

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
theorem _root_.solution {n : ℕ} (x : Fin n → ℂ) : ((nsq x : ℝ) : ℂ) = star x ⬝ᵥ x := by
  simp [nsq, dotProduct, Complex.normSq_eq_conj_mul_self]
end PI.PolynomialProperness.CoreW

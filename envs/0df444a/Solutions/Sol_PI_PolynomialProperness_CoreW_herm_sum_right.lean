-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.herm_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:21:25.621805+00:00
-- url     : https://prove2.me/submissions/d4fb518b-23a3-4142-8ad6-40615c47763a

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
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
namespace PI.PolynomialProperness.CoreW
theorem _root_.solution (hH : Hᴴ = H) {ι : Type} [Fintype ι] (f : ι → Fin n → ℂ) (v : Fin n → ℂ) :
    herm H v (∑ i, f i) = ∑ i, herm H v (f i) := by
  simp [herm, star_sum, sum_dotProduct]
end PI.PolynomialProperness.CoreW

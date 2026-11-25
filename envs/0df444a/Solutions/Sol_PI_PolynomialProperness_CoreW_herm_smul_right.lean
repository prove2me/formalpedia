-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.herm_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:31.433708+00:00
-- url     : https://prove2.me/submissions/ab33ead6-38c2-42bd-9ec6-6346a48beea6

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
theorem _root_.solution (hH : Hᴴ = H) (c : ℂ) (v w : Fin n → ℂ) :
    herm H v (c • w) = conj c * herm H v w := by
  simp [herm, star_smul, smul_dotProduct]
end PI.PolynomialProperness.CoreW

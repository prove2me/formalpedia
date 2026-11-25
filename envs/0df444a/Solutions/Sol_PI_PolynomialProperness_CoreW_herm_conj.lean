-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.herm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:03:43.709526+00:00
-- url     : https://prove2.me/submissions/59a32731-6acf-44df-ab24-972ff45eafef

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
theorem _root_.solution (hH : Hᴴ = H) (v w : Fin n → ℂ) : conj (herm H v w) = herm H w v := by
  unfold herm
  rw [← Complex.star_def, Matrix.star_dotProduct, star_star, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, hH]
end PI.PolynomialProperness.CoreW

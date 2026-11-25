-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.herm_H_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:14:57.071799+00:00
-- url     : https://prove2.me/submissions/1402ebee-a8ac-4aba-bef4-649d28dfe36a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Theorems.Thm_PI_PolynomialProperness_CoreW_nsq_ofReal
import Theorems.Thm_PI_PolynomialProperness_CoreW_star_H_dot

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
theorem _root_.solution (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) :
    herm H v (H *ᵥ v) = ((nsq v : ℝ) : ℂ) := by
  unfold herm
  rw [star_H_dot H hH hHH, nsq_ofReal]
end PI.PolynomialProperness.CoreW

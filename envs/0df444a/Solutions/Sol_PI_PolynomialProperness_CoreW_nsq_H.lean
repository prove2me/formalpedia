-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.nsq_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:42.882643+00:00
-- url     : https://prove2.me/submissions/4305d942-d0fd-4ea1-a200-6b6ec07b7327

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
theorem _root_.solution (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) : nsq (H *ᵥ v) = nsq v := by
  have h : ((nsq (H *ᵥ v) : ℝ) : ℂ) = ((nsq v : ℝ) : ℂ) := by
    rw [nsq_ofReal, nsq_ofReal, star_H_dot H hH hHH v]
  exact_mod_cast h
end PI.PolynomialProperness.CoreW

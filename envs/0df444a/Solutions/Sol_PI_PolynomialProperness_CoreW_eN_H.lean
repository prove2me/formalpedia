-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.eN_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:39:45.842527+00:00
-- url     : https://prove2.me/submissions/0273d255-68a4-4833-9333-ae5a3eebcc46

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_nonneg
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_sq
import Theorems.Thm_PI_PolynomialProperness_CoreW_nsq_H

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
theorem _root_.solution (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) : eN (H *ᵥ v) = eN v := by
  have h : eN (H *ᵥ v) ^ 2 = eN v ^ 2 := by rw [eN_sq, eN_sq, nsq_H H hH hHH]
  exact (pow_left_inj₀ (eN_nonneg _) (eN_nonneg _) two_ne_zero).mp h
end PI.PolynomialProperness.CoreW

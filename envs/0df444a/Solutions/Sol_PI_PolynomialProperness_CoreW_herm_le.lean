-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.herm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:58:10.84665+00:00
-- url     : https://prove2.me/submissions/fa16c886-bc6b-4b33-9001-c8ae60e72dcf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Theorems.Thm_PI_PolynomialProperness_CoreW_dot_le
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_H

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
theorem _root_.solution (hH : Hᴴ = H) (hHH : H * H = 1) (v w : Fin n → ℂ) :
    ‖herm H v w‖ ≤ eN v * eN w := by
  unfold herm
  calc ‖star w ⬝ᵥ (H *ᵥ v)‖ ≤ eN w * eN (H *ᵥ v) := dot_le _ _
    _ = eN v * eN w := by rw [eN_H H hH hHH, mul_comm]
end PI.PolynomialProperness.CoreW

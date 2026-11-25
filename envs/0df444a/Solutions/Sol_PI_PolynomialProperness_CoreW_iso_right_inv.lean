-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.iso_right_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:04:06.196397+00:00
-- url     : https://prove2.me/submissions/459457a5-b477-45ed-bf7a-d193447038ce

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_IsoRightInv

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
open PI PI.PolynomialProperness
open PI.PolynomialProperness.CoreW
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.PolynomialProperness.CoreW
theorem _root_.solution (H s : Matrix (Fin n) (Fin n) ℂ) (hHH : H * H = 1) (hs : sᴴ * H * s = H) :
    s * (H * sᴴ * H) = 1 := by
  have h : H * sᴴ * H * s = 1 := by
    rw [mul_assoc, mul_assoc, ← mul_assoc sᴴ, hs, hHH]
  rw [← Matrix.inv_eq_left_inv h]
  exact Matrix.mul_nonsing_inv s (Matrix.isUnit_det_of_left_inverse h)
end PI.PolynomialProperness.CoreW

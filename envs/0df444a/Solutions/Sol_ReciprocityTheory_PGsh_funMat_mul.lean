-- Prove2me | solution 1 for ReciprocityTheory.PGsh.funMat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:45:36.091273+00:00
-- url     : https://prove2.me/submissions/8b4c906d-7c5c-4897-b2d7-82b5f69a1d17

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (ρ ρ' : Fin n → Fin n) : funMat ρ * funMat ρ' = funMat (ρ ∘ ρ') := by
  ext a c
  simp only [funMat, Matrix.mul_apply, Matrix.of_apply, Function.comp_apply, mul_ite, mul_one,
    mul_zero]
  simp
end ReciprocityTheory.PGsh

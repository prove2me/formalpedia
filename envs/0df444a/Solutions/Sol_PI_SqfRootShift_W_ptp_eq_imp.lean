-- Prove2me | solution 1 for PI.SqfRootShift.W.ptp_eq_imp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:31:31.592515+00:00
-- url     : https://prove2.me/submissions/76eed8af-7c2e-4865-b0d9-ed3897145772

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountA
import Theorems.Thm_PI_SqfRootShift_W_ptp_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
namespace PI.SqfRootShift.W
theorem _root_.solution {M : Type*} [CommMonoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x y : M)
    (hx : 0 < orderOf x) (hy : 0 < orderOf y) (h : primeToPart ℓ x = primeToPart ℓ y) :
    ∃ j, x ^ (ℓ ^ j) = y ^ (ℓ ^ j) := by
  refine ⟨(orderOf x).factorization ℓ + (orderOf y).factorization ℓ, ?_⟩
  rw [pow_add, pow_mul, ptp_pow ℓ hℓ x hx, h, ← pow_mul, mul_comm, pow_mul,
    ← ptp_pow ℓ hℓ y hy, ← pow_mul, ← pow_add, add_comm]
end PI.SqfRootShift.W

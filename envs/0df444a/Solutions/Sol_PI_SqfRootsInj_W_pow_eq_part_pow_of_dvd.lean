-- Prove2me | solution 1 for PI.SqfRootsInj.W.pow_eq_part_pow_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:26.082669+00:00
-- url     : https://prove2.me/submissions/6cacd44e-efb8-4a22-aacb-eb7fff6a3fe5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_ClaimOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase
import Theorems.Thm_PI_SqfRootsInj_W_pow_eq_part_pow

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
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution {M : Type*} [Monoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x : M) (N : ℕ)
    (hN : N ≠ 0) (hxN : orderOf x ∣ N) :
    x ^ (ℓ ^ padicValNat ℓ N) = (primeToPart ℓ x) ^ (ℓ ^ padicValNat ℓ N) := by
  have hx : 0 < orderOf x := Nat.pos_of_ne_zero fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hxN))
  have hle : (orderOf x).factorization ℓ ≤ padicValNat ℓ N := by
    rw [← Nat.factorization_def N hℓ]
    exact (Nat.factorization_le_iff_dvd hx.ne' hN).2 hxN ℓ
  have key := pow_eq_part_pow ℓ hℓ x hx
  rw [← Nat.add_sub_cancel' hle, pow_add, pow_mul, pow_mul, key]
end PI.SqfRootsInj.W

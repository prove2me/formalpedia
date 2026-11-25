-- Prove2me | solution 1 for PI.KerFourSqW.quat_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:45.890595+00:00
-- url     : https://prove2.me/submissions/0eb098b6-0058-4615-a393-ef51d79785eb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul
import Theorems.Thm_PI_KerFourSqW_sum_mul_cast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open PI PI.KerFourSqW
namespace PI.KerFourSqW
theorem _root_.solution {L F : Type*} [Field L] [CharZero L] [FunLike F L L] [RingHomClass F L L] (c : F) (Q : Matrix (Fin 4) (Fin 4) ℚ) (a : ℚ)
    (hQ : Qᵀ * Q = a • (1 : Matrix (Fin 4) (Fin 4) ℚ)) (x y : Fin 4 → L) :
    ∑ b, (∑ j, (Q b j : L) * x j) * c (∑ k, (Q b k : L) * y k) = (a : L) * ∑ j, x j * c (y j) := by
  have hc : ∀ b, c (∑ k, (Q b k : L) * y k) = ∑ k, (Q b k : L) * c (y k) := by
    intro b
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_ratCast]
  simp_rw [hc, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  have : ∀ j, ∑ b, ∑ k, (Q b j : L) * x j * ((Q b k : L) * c (y k))
      = ∑ k, (∑ b, (Q b j : L) * (Q b k : L)) * (x j * c (y k)) := by
    intro j
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp_rw [this, sum_mul_cast Q a hQ, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.mul_sum]
end PI.KerFourSqW

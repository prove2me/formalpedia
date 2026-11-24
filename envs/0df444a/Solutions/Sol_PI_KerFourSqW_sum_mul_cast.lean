-- Prove2me | solution 1 for PI.KerFourSqW.sum_mul_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:24:43.892366+00:00
-- url     : https://prove2.me/submissions/95ece0d8-57b2-4d39-a112-0f72cb1fb0b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul

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
theorem _root_.solution {L : Type*} [Field L] [CharZero L] (Q : Matrix (Fin 4) (Fin 4) ℚ) (a : ℚ)
    (hQ : Qᵀ * Q = a • (1 : Matrix (Fin 4) (Fin 4) ℚ)) (j k : Fin 4) :
    ∑ b, (Q b j : L) * (Q b k : L) = if j = k then (a : L) else 0 := by
  have h := congrFun (congrFun hQ j) k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul] at h
  have h' : ((∑ b, Q b j * Q b k : ℚ) : L) = ((a * if j = k then 1 else 0 : ℚ) : L) := by rw [h]
  push_cast at h'
  rw [h']
  split_ifs <;> simp
end PI.KerFourSqW

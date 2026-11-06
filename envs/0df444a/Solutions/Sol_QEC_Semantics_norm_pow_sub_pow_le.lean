-- Prove2me | solution 1 for QEC.Semantics.norm_pow_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:42:48.968198+00:00
-- url     : https://prove2.me/submissions/056ee116-ea12-4cfc-af14-a0cec3a475a5

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Theorems.Thm_QEC_Semantics_pow_sub_pow_eq_sum

set_option autoImplicit false
open QEC QEC.Semantics
open Filter
open scoped Topology
noncomputable section
variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra Complex A] [CompleteSpace A]
namespace QEC.Semantics
theorem _root_.solution (x y : A) (n : Nat) :
    ‖x ^ n - y ^ n‖ ≤
      ∑ k ∈ Finset.range n,
        ‖x‖ ^ k * ‖x - y‖ * ‖y‖ ^ (n - 1 - k) := by
  rw [pow_sub_pow_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _hk => ?_)
  calc
    ‖x ^ k * (x - y) * y ^ (n - 1 - k)‖ ≤
        ‖x ^ k * (x - y)‖ * ‖y ^ (n - 1 - k)‖ := norm_mul_le _ _
    _ ≤ (‖x ^ k‖ * ‖x - y‖) * ‖y ^ (n - 1 - k)‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ (‖x‖ ^ k * ‖x - y‖) * ‖y‖ ^ (n - 1 - k) := by
      gcongr
      · exact norm_pow_le x k
      · exact norm_pow_le y (n - 1 - k)
    _ = ‖x‖ ^ k * ‖x - y‖ * ‖y‖ ^ (n - 1 - k) := rfl
end QEC.Semantics

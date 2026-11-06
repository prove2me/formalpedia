-- Prove2me | solution 1 for QEC.Semantics.norm_normedSpace_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:39:10.758256+00:00
-- url     : https://prove2.me/submissions/8be0ae54-76a7-4c38-b849-578b9dfb7c38

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter

set_option autoImplicit false
open QEC QEC.Semantics
open Filter
open scoped Topology
noncomputable section
variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra Complex A] [CompleteSpace A]
namespace QEC.Semantics
theorem _root_.solution (x : A) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  rw [← (NormedSpace.exp_series_hasSum_exp' (𝕂 := Complex) x).tsum_eq]
  calc
    ‖∑' n : Nat, ((Nat.factorial n : Complex)⁻¹ • x ^ n)‖ ≤
        ∑' n : Nat, ‖((Nat.factorial n : Complex)⁻¹ • x ^ n)‖ :=
      norm_tsum_le_tsum_norm (by
        simpa using NormedSpace.norm_expSeries_summable' (𝕂 := Complex) x)
    _ ≤ ∑' n : Nat, ‖x‖ ^ n / Nat.factorial n := by
      exact (NormedSpace.norm_expSeries_summable' (𝕂 := Complex) x).tsum_le_tsum
        (fun n => by
          rw [norm_smul]
          calc
            ‖(Nat.factorial n : Complex)⁻¹‖ * ‖x ^ n‖ ≤
                ‖(Nat.factorial n : Complex)⁻¹‖ * ‖x‖ ^ n :=
              mul_le_mul_of_nonneg_left (norm_pow_le x n) (norm_nonneg _)
            _ = ‖x‖ ^ n / Nat.factorial n := by
              simp [div_eq_mul_inv, mul_comm])
        (Real.summable_pow_div_factorial ‖x‖)
    _ = Real.exp ‖x‖ := by
      simpa [Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp ‖x‖).tsum_eq
end QEC.Semantics

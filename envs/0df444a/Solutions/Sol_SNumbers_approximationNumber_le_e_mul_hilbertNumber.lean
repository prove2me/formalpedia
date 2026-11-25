-- Prove2me | solution 1 for SNumbers.approximationNumber_le_e_mul_hilbertNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:22:39.055202+00:00
-- url     : https://prove2.me/submissions/5e4086da-8533-43c4-a863-5625c180ee40

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_approximationNumber_le_mul_hilbertNumber
public import Theorems.Thm_SNumbers_hilbertNumber_nonneg

section
@[expose] public section
universe u
open ContinuousLinearMap
open scoped Pointwise
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
private lemma pow_self_pos (n : ℕ) : (0 : ℝ) < (n : ℝ) ^ n := by
  cases n with
  | zero => norm_num
  | succ m => exact pow_pos (by exact_mod_cast Nat.succ_pos m) _
private lemma ratio_le_exp_mul (n : ℕ) :
    ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n ≤ Real.exp 1 * ((n : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 : 1 + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
      have := Real.add_one_le_exp (1 / (n : ℝ)); linarith
    have h2 : (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 := by
      calc (1 + 1 / (n : ℝ)) ^ n
          ≤ Real.exp (1 / (n : ℝ)) ^ n := pow_le_pow_left₀ (by positivity) h1 n
        _ = Real.exp ((n : ℝ) * (1 / (n : ℝ))) := (Real.exp_nat_mul _ n).symm
        _ = Real.exp 1 := by rw [mul_one_div, div_self hN.ne']
    have h3 : ((n : ℝ) + 1) ^ n ≤ Real.exp 1 * (n : ℝ) ^ n := by
      have hfac : (n : ℝ) + 1 = (n : ℝ) * (1 + 1 / (n : ℝ)) := by field_simp
      calc ((n : ℝ) + 1) ^ n = (n : ℝ) ^ n * (1 + 1 / (n : ℝ)) ^ n := by
            rw [hfac, mul_pow]
        _ ≤ (n : ℝ) ^ n * Real.exp 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Real.exp 1 * (n : ℝ) ^ n := mul_comm _ _
    rw [div_le_iff₀ (pow_self_pos n)]
    calc ((n : ℝ) + 1) ^ (n + 1) = ((n : ℝ) + 1) ^ n * ((n : ℝ) + 1) := pow_succ _ _
      _ ≤ Real.exp 1 * (n : ℝ) ^ n * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = Real.exp 1 * ((n : ℝ) + 1) * (n : ℝ) ^ n := by ring
section Border
variable {k : ℕ}
variable (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (x : X)
  (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (b : Y →L[𝕜] 𝕜) (lam mu : ℝ)
end Border
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open scoped Pointwise
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ Real.exp 1 * ((n : ℝ) + 1) * hilbertNumber S n :=
  (approximationNumber_le_mul_hilbertNumber S n).trans
    (mul_le_mul_of_nonneg_right (ratio_le_exp_mul n) (hilbertNumber_nonneg S n))
end SNumbers

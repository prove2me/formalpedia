-- Prove2me | solution 1 for SNumbers.approximationNumber_le_mul_hilbertNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:58:49.318666+00:00
-- url     : https://prove2.me/submissions/df06fe78-43e3-496e-b9ba-ac2a7748d704

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_detNumber_succ_le_hilbertNumber_mul
public import Theorems.Thm_SNumbers_approximationNumber_mul_detNumber_le_detNumber_succ
public import Theorems.Thm_SNumbers_detNumber_pos_of_approximationNumber_pos
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
    approximationNumber S n
      ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n := by
  rcases le_or_gt (approximationNumber S n) 0 with hle | hpos
  · exact hle.trans (mul_nonneg (div_nonneg (by positivity) (pow_self_pos n).le)
      (hilbertNumber_nonneg S n))
  -- The determinant quantities are positive, so the chain can be divided by `Δₙ(S)`.
  have hΔ : 0 < detNumber S n :=
    detNumber_pos_of_approximationNumber_pos S hpos n (Nat.le_succ n)
  have hchain : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * approximationNumber S n *
      detNumber S n ≤ hilbertNumber S n * detNumber S n :=
    (approximationNumber_mul_detNumber_le_detNumber_succ S n).trans
      (detNumber_succ_le_hilbertNumber_mul S n)
  have hkey : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * approximationNumber S n
      ≤ hilbertNumber S n := le_of_mul_le_mul_right hchain hΔ
  -- Rearrange.
  rw [div_mul_eq_mul_div,
    div_le_iff₀ (pow_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) (n + 1))] at hkey
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_self_pos n)]
  calc approximationNumber S n * (n : ℝ) ^ n
      = (n : ℝ) ^ n * approximationNumber S n := mul_comm _ _
    _ ≤ hilbertNumber S n * ((n : ℝ) + 1) ^ (n + 1) := hkey
    _ = ((n : ℝ) + 1) ^ (n + 1) * hilbertNumber S n := mul_comm _ _
end SNumbers

-- Prove2me | solution 1 for SNumbers.detNumber_pos_of_approximationNumber_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:44:17.943879+00:00
-- url     : https://prove2.me/submissions/d34ac908-1457-4d35-9575-982c04160a5c

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_detNumber_zero
public import Theorems.Thm_SNumbers_approximationNumber_mul_detNumber_le_detNumber_succ
public import Theorems.Thm_P2M_SNumbers_approximationNumber_antitone__260bc309c16c

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
private lemma growth_ratio_pos (k : ℕ) :
    (0 : ℝ) < (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) :=
  div_pos (pow_self_pos k) (pow_pos (by positivity) _)
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
theorem _root_.solution (S : X →L[𝕜] Y) {n : ℕ}
    (h : 0 < approximationNumber S n) : ∀ k, k ≤ n + 1 → 0 < detNumber S k := by
  intro k
  induction k with
  | zero => intro _; rw [detNumber_zero]; exact one_pos
  | succ m ih =>
    intro hm
    have hm' : m ≤ n := Nat.lt_succ_iff.mp hm
    have ham : 0 < approximationNumber S m :=
      h.trans_le (approximationNumber_antitone' hm')
    have hpos : 0 < (m : ℝ) ^ m / ((m : ℝ) + 1) ^ (m + 1) *
        approximationNumber S m * detNumber S m :=
      mul_pos (mul_pos (growth_ratio_pos m) ham) (ih (hm'.trans (Nat.le_succ n)))
    exact hpos.trans_le (approximationNumber_mul_detNumber_le_detNumber_succ S m)
end SNumbers

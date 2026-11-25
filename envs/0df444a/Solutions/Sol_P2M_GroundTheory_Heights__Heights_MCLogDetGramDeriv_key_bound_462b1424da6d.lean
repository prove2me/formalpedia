-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCLogDetGramDeriv_key_bound_462b1424da6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:24.033375+00:00
-- url     : https://prove2.me/submissions/1bd86e68-fd73-47f2-ad83-57f54c6c3005

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramDeriv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCLogDetGramDeriv_constK_pos_9ffca9a7baa6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MCLogDetGramDeriv
namespace GroundTheory.Heights₂.Heights.MCLogDetGramDeriv
theorem _root_.solution (g k : ℕ) (a b x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    (k.factorial : ℝ) * k * ((g : ℝ) ^ 2 * a ^ 2 * x) ^ (k - 1) *
        ((g : ℝ) ^ 2 * (2 * a ^ 2 * x + a ^ 2 * ((g : ℝ) ^ 2 * x ^ 2 * b))) ≤
      constK g k * (1 + a) ^ (2 * k) * (1 + x) ^ (k + 1) * (1 + b) := by
  rcases k with _ | n
  · simp only [Nat.cast_zero, mul_zero, zero_mul]
    have := constK_pos g 0
    positivity
  · simp only [Nat.add_sub_cancel]
    have hx1 : 1 ≤ 1 + x := by linarith
    have hA : (a ^ 2) ^ n * a ^ 2 ≤ (1 + a) ^ (2 * (n + 1)) := by
      rw [← pow_succ, pow_mul]
      gcongr
      linarith
    have hX1 : x ^ (n + 1) ≤ (1 + x) ^ (n + 1 + 1) :=
      (pow_le_pow_left₀ hx (by linarith) _).trans (pow_le_pow_right₀ hx1 (by omega))
    have hX2 : x ^ (n + 2) ≤ (1 + x) ^ (n + 1 + 1) := pow_le_pow_left₀ hx (by linarith) _
    have hbr : 2 * x ^ (n + 1) + (g : ℝ) ^ 2 * x ^ (n + 2) * b ≤
        ((g : ℝ) ^ 2 + 2) * ((1 + x) ^ (n + 1 + 1) * (1 + b)) := by
      have h1 : 2 * x ^ (n + 1) ≤ 2 * ((1 + x) ^ (n + 1 + 1) * (1 + b)) := by
        have : (1 + x) ^ (n + 1 + 1) ≤ (1 + x) ^ (n + 1 + 1) * (1 + b) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
        linarith
      have h2 : (g : ℝ) ^ 2 * x ^ (n + 2) * b ≤
          (g : ℝ) ^ 2 * ((1 + x) ^ (n + 1 + 1) * (1 + b)) := by
        rw [mul_assoc]
        gcongr
        have : 0 ≤ x ^ (n + 2) := by positivity
        nlinarith
      linarith
    have hP : 0 ≤ ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2) ^ (n + 1) := by
      positivity
    have hbr0 : 0 ≤ 2 * x ^ (n + 1) + (g : ℝ) ^ 2 * x ^ (n + 2) * b := by positivity
    calc ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2 * a ^ 2 * x) ^ n *
          ((g : ℝ) ^ 2 * (2 * a ^ 2 * x + a ^ 2 * ((g : ℝ) ^ 2 * x ^ 2 * b)))
        = (((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2) ^ (n + 1)) *
            ((a ^ 2) ^ n * a ^ 2) * (2 * x ^ (n + 1) + (g : ℝ) ^ 2 * x ^ (n + 2) * b) := by
          ring
      _ ≤ (((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2) ^ (n + 1)) *
            (1 + a) ^ (2 * (n + 1)) * (((g : ℝ) ^ 2 + 2) * ((1 + x) ^ (n + 1 + 1) * (1 + b))) := by
          gcongr
      _ = (((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2) ^ (n + 1) *
            ((g : ℝ) ^ 2 + 2)) * ((1 + a) ^ (2 * (n + 1)) * (1 + x) ^ (n + 1 + 1) * (1 + b)) := by
          ring
      _ ≤ constK g (n + 1) * ((1 + a) ^ (2 * (n + 1)) * (1 + x) ^ (n + 1 + 1) * (1 + b)) := by
          gcongr
          unfold constK
          push_cast
          linarith
      _ = constK g (n + 1) * (1 + a) ^ (2 * (n + 1)) * (1 + x) ^ (n + 1 + 1) * (1 + b) := by ring
end GroundTheory.Heights₂.Heights.MCLogDetGramDeriv

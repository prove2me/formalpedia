-- Prove2me | solution 1 for WeilDefect.RPB108.mixed_pairing_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:59:39.929204+00:00
-- url     : https://prove2.me/submissions/5cb686a4-44ff-44ba-82b1-a9ee45b5acfe

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution (p q : ℂ) (a b V M : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hV : 0 ≤ V)
    (hp : ‖p‖^2 ≤ a*V) (hq : ‖q‖^2 ≤ b*V)
    (hM : Real.sqrt a+Real.sqrt b ≤ M) :
    ‖p-q‖ ≤ M*Real.sqrt V := by
  have bound (r : ℂ) (c : ℝ) (hc : 0 ≤ c) (hr : ‖r‖^2 ≤ c*V) :
      ‖r‖ ≤ Real.sqrt c*Real.sqrt V := by
    have he : (Real.sqrt c*Real.sqrt V)^2 = c*V := by
      rw [mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hV]
    have hn : 0 ≤ Real.sqrt c*Real.sqrt V := by positivity
    nlinarith only [he, hn, hr, norm_nonneg r]
  calc
    ‖p-q‖ ≤ ‖p‖+‖q‖ := norm_sub_le _ _
    _ ≤ Real.sqrt a*Real.sqrt V+Real.sqrt b*Real.sqrt V :=
      add_le_add (bound p a ha hp) (bound q b hb hq)
    _ = (Real.sqrt a+Real.sqrt b)*Real.sqrt V := by ring
    _ ≤ M*Real.sqrt V := mul_le_mul_of_nonneg_right hM (Real.sqrt_nonneg _)

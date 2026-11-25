-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_pi_pow_mul_two_pow_div_doubleFactorial_le_six_35886cc5d309
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:44.168393+00:00
-- url     : https://prove2.me/submissions/47e7549f-ad54-4f6c-9196-a2007884d150

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSmallBallVolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Real Module
open scoped Nat
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (k : ℕ) :
    π ^ k * 2 ^ (k + 1) / ((2 * k + 1)‼ : ℝ) ≤ 6 := by
  have hπ := pi_lt_d2
  have hπ0 := pi_pos
  have step : ∀ k, 2 ≤ k → π ^ (k + 1) * 2 ^ (k + 1 + 1) / ((2 * (k + 1) + 1)‼ : ℝ) ≤
      π ^ k * 2 ^ (k + 1) / ((2 * k + 1)‼ : ℝ) := by
    intro k hk
    have hk' : (7 : ℝ) ≤ 2 * (k : ℝ) + 3 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [he, Nat.doubleFactorial_add_two, Nat.cast_mul, pow_succ, pow_succ (2 : ℝ) (k + 1)]
    have hf : (0 : ℝ) < ((2 * k + 1)‼ : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
    rw [div_le_div_iff₀ (by positivity) hf]
    push_cast
    have hp : 0 < π ^ k * 2 ^ (k + 1) := by positivity
    nlinarith [mul_pos hp hf]
  have h2 : π ^ 2 * 2 ^ (2 + 1) / ((2 * 2 + 1)‼ : ℝ) ≤ 6 := by
    norm_num [Nat.doubleFactorial]
    nlinarith
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k
    · norm_num [Nat.doubleFactorial]
    · norm_num [Nat.doubleFactorial]; linarith
  · induction k, hk using Nat.le_induction with
    | base => exact h2
    | succ n hn ih => exact (step n hn).trans ih
end GroundTheory.Heights₂.Heights.HilbertSamuel

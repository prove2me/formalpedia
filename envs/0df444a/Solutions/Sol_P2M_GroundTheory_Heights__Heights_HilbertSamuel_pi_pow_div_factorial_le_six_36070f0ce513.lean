-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_pi_pow_div_factorial_le_six_36070f0ce513
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:43.443039+00:00
-- url     : https://prove2.me/submissions/88893f5d-1cd3-4450-8830-9e553dc727e3

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
theorem _root_.solution (k : ℕ) : π ^ k / (k ! : ℝ) ≤ 6 := by
  have hπ := pi_lt_d2
  have hπ0 := pi_pos
  have step : ∀ k, 3 ≤ k → π ^ (k + 1) / ((k + 1) ! : ℝ) ≤ π ^ k / (k ! : ℝ) := by
    intro k hk
    have hk' : (4 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have hf : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_div_iff₀ (by positivity) hf]
    push_cast
    have hp : 0 < π ^ k := pow_pos hπ0 k
    nlinarith [mul_pos hp hf]
  have h3 : π ^ 3 / ((3 : ℕ) ! : ℝ) ≤ 6 := by
    norm_num [Nat.factorial]
    nlinarith [sq_nonneg π, mul_pos hπ0 hπ0]
  rcases lt_or_ge k 3 with hk | hk
  · interval_cases k
    · norm_num
    · norm_num; linarith
    · norm_num [Nat.factorial]; nlinarith
  · induction k, hk using Nat.le_induction with
    | base => exact h3
    | succ n hn ih => exact (step n hn).trans ih
end GroundTheory.Heights₂.Heights.HilbertSamuel

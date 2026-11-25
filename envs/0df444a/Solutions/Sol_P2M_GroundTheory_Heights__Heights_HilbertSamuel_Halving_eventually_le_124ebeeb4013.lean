-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_Halving_eventually_le_124ebeeb4013
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:00.313945+00:00
-- url     : https://prove2.me/submissions/6d236033-1b6a-4953-a1cc-0b95c29ec5c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHalving

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
open Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace Halving
theorem _root_.solution (a : ℕ → ℝ) (C : ℝ) (hC : ∀ n, |a n| ≤ C)
    (hh : Tendsto (fun n ↦ a (2 * n) - a n / 2) atTop (𝓝 0))
    (hs : Tendsto (fun n ↦ a (n + 1) - a n) atTop (𝓝 0)) (k : ℕ) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n| ≤ C / 2 ^ k + ε := by
  induction k with
  | zero =>
    intro ε hε
    exact ⟨0, fun n _ ↦ by simpa using (hC n).trans (by linarith)⟩
  | succ k ih =>
    intro ε hε
    obtain ⟨N, hN⟩ := ih (ε / 4) (by positivity)
    obtain ⟨M₁, hM₁⟩ := Metric.tendsto_atTop.mp hh (ε / 4) (by positivity)
    obtain ⟨M₂, hM₂⟩ := Metric.tendsto_atTop.mp hs (ε / 4) (by positivity)
    refine ⟨2 * (N + M₁ + M₂), fun m hm ↦ ?_⟩
    have hpow : C / 2 ^ (k + 1) = C / 2 ^ k / 2 := by rw [pow_succ, div_div]

    have even : ∀ n ≥ N + M₁ + M₂, |a (2 * n)| ≤ C / 2 ^ (k + 1) + ε / 2 := by
      intro n hn
      have h1 := hN n (by omega)
      have h2 := hM₁ n (by omega)
      rw [Real.dist_eq, sub_zero] at h2
      have h3 : |a (2 * n)| ≤ |a (2 * n) - a n / 2| + |a n| / 2 := by
        have := abs_add_le (a (2 * n) - a n / 2) (a n / 2)
        rw [sub_add_cancel, abs_div, abs_two] at this
        exact this
      rw [hpow]
      linarith
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
    · exact (even n (by omega)).trans (by linarith)
    · have he := even n (by omega)
      have h4 := hM₂ (2 * n) (by omega)
      rw [Real.dist_eq, sub_zero] at h4
      have h5 : |a (2 * n + 1)| ≤ |a (2 * n + 1) - a (2 * n)| + |a (2 * n)| := by
        have := abs_add_le (a (2 * n + 1) - a (2 * n)) (a (2 * n))
        rwa [sub_add_cancel] at this
      linarith
end Halving
end GroundTheory.Heights₂.Heights.HilbertSamuel

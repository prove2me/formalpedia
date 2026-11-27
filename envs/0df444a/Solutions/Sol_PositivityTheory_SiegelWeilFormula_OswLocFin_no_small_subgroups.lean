-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.OswLocFin.no_small_subgroups
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:33.941397+00:00
-- url     : https://prove2.me/submissions/64561b7a-7bac-4ac1-86b7-027022bffe0f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalInvariantNeighborhoods_SmallSub
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_OswLocFin_eq_one_of_re_pow_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.OswLocFin
namespace PositivityTheory.SiegelWeilFormula.OswLocFin
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
    (χ : K → ℂ) (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1)
    (hn : ∀ x, ‖χ x‖ = 1) : ∃ ε > 0, ∀ t : K, ‖t‖ ≤ ε → χ t = 1 := by
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.1 hc 0 (1 / 2) (by norm_num)
  refine ⟨δ / 2, half_pos hδ, fun t ht => ?_⟩
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (1 : K) 1
    rw [one_add_one_eq_two, norm_one, max_self] at this
    exact this
  have hsmall : ∀ k : ℕ, ‖(2 : K) ^ k * t‖ ≤ δ / 2 := fun k => by
    rw [norm_mul, norm_pow]
    calc ‖(2 : K)‖ ^ k * ‖t‖ ≤ 1 * ‖t‖ := by
          gcongr; exact pow_le_one₀ (norm_nonneg _) h2
      _ ≤ δ / 2 := by rw [one_mul]; exact ht
  have hpow : ∀ k : ℕ, χ ((2 : K) ^ k * t) = χ t ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show (2 : K) ^ (k + 1) * t = (2 : K) ^ k * t + (2 : K) ^ k * t by ring, hadd, ih, ← pow_add]
      congr 1
      ring
  have hre : ∀ k : ℕ, 1 / 2 < (χ t ^ (2 ^ k)).re := by
    intro k
    rw [← hpow k]
    have hd := hδc ((2 : K) ^ k * t) (by rw [dist_zero_right]; linarith [hsmall k])
    rw [h0, dist_eq_norm] at hd
    have := Complex.re_le_norm (1 - χ ((2 : K) ^ k * t))
    rw [norm_sub_rev] at this
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  exact eq_one_of_re_pow_two (χ t) (hn t) hre
end PositivityTheory.SiegelWeilFormula.OswLocFin

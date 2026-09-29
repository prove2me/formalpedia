-- Prove2me | solution 1 for Rudin.ch03_ratio_test_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T05:16:44.312202+00:00
-- url     : https://prove2.me/submissions/d21757e9-0c47-439b-89d4-49d2664c581c

import Mathlib
import Definitions.Def_Rudin_ch03_series

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace RudinFix3

open Filter Topology Rudin

/-- Terms of a convergent series tend to zero. -/
theorem term_tendsto_zero {a : ℕ → ℂ} (h : SeriesConverges a) : Tendsto a atTop (𝓝 0) := by
  obtain ⟨s, hs⟩ := h
  have h1 : Tendsto (fun n => partialSum a (n + 1)) atTop (𝓝 s) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have h2 : ∀ n, a n = partialSum a (n + 1) - partialSum a n := by
    intro n
    rw [partialSum, partialSum, Finset.sum_range_succ]
    ring
  have h3 : Tendsto (fun n => partialSum a (n + 1) - partialSum a n) atTop (𝓝 (s - s)) := h1.sub hs
  rw [sub_self] at h3
  exact h3.congr fun n => (h2 n).symm

theorem ch03_ratio_test (a : ℕ → ℂ) :
    ((∀ n, a n ≠ 0) →
        limsup (fun n => ((‖a (n + 1)‖ / ‖a n‖ : ℝ) : EReal)) atTop < 1 → SeriesConverges a) ∧
    ((∃ N, ∀ n ≥ N, a n ≠ 0 ∧ ‖a n‖ ≤ ‖a (n + 1)‖) → ¬ SeriesConverges a) := by
  constructor
  · -- convergence half
    intro hne hlim
    obtain ⟨β, hLβ, hβ1⟩ := EReal.exists_between_coe_real hlim
    have hev : ∀ᶠ n in atTop, ‖a (n + 1)‖ / ‖a n‖ < β := by
      have h := eventually_lt_of_limsup_lt hLβ
      filter_upwards [h] with n hn
      exact_mod_cast hn
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    have hpos : ∀ n, 0 < ‖a n‖ := fun n => norm_pos_iff.2 (hne n)
    have hβ0 : 0 < β := by
      have h1 := hN N le_rfl
      have h2 : 0 ≤ ‖a (N + 1)‖ / ‖a N‖ := by positivity
      linarith
    have hβ1' : β < 1 := by exact_mod_cast hβ1
    have hstep : ∀ n ≥ N, ‖a (n + 1)‖ < β * ‖a n‖ := by
      intro n hn
      have h := hN n hn
      rw [div_lt_iff₀ (hpos n)] at h
      linarith
    have hgeo : ∀ k : ℕ, ‖a (N + k)‖ ≤ ‖a N‖ * β ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h1 : ‖a (N + k + 1)‖ < β * ‖a (N + k)‖ := hstep (N + k) (Nat.le_add_right _ _)
        have h2 : β * ‖a (N + k)‖ ≤ β * (‖a N‖ * β ^ k) :=
          mul_le_mul_of_nonneg_left ih hβ0.le
        calc ‖a (N + (k + 1))‖ = ‖a (N + k + 1)‖ := by ring_nf
          _ ≤ β * (‖a N‖ * β ^ k) := le_of_lt (lt_of_lt_of_le h1 h2)
          _ = ‖a N‖ * β ^ (k + 1) := by ring
    have hsum_shift : Summable (fun k : ℕ => ‖a (N + k)‖) := by
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) hgeo ?_
      exact (summable_geometric_of_lt_one hβ0.le hβ1').mul_left _
    have hsumnorm : Summable (fun n : ℕ => ‖a n‖) := by
      rw [← summable_nat_add_iff N]
      simpa [add_comm] using hsum_shift
    have hsa : Summable a := Summable.of_norm hsumnorm
    exact ⟨∑' n, a n, hsa.hasSum.tendsto_sum_nat⟩
  · -- divergence half
    rintro ⟨N, hN⟩ hconv
    have h0 : Tendsto a atTop (𝓝 0) := term_tendsto_zero hconv
    have hmono : ∀ n, N ≤ n → ‖a N‖ ≤ ‖a n‖ := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => exact le_rfl
      | succ n hn ih => exact ih.trans (hN n hn).2
    have hpos : 0 < ‖a N‖ := norm_pos_iff.2 (hN N le_rfl).1
    rw [Metric.tendsto_atTop] at h0
    obtain ⟨M, hM⟩ := h0 ‖a N‖ hpos
    have h1 := hM (max M N) (le_max_left _ _)
    rw [dist_zero_right] at h1
    have h2 := hmono (max M N) (le_max_right _ _)
    linarith

end RudinFix3

open Filter Topology Rudin in
theorem solution (a : ℕ → ℂ) :
    ((∀ n, a n ≠ 0) →
        limsup (fun n => ((‖a (n + 1)‖ / ‖a n‖ : ℝ) : EReal)) atTop < 1 → SeriesConverges a) ∧
    ((∃ N, ∀ n ≥ N, a n ≠ 0 ∧ ‖a n‖ ≤ ‖a (n + 1)‖) → ¬ SeriesConverges a) :=
  RudinFix3.ch03_ratio_test a

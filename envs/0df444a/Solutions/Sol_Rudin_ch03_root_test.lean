-- Prove2me | solution 1 for Rudin.ch03_root_test
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-13T14:47:41.319913+00:00
-- url     : https://prove2.me/submissions/4e5f4ee4-ce8e-4362-8dc4-81bc777f9e3f

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

open Rudin in
/-- If the series `∑ aₙ` converges then its terms tend to `0`. -/
private theorem tendsto_zero_of_seriesConverges {a : ℕ → ℂ} (h : SeriesConverges a) :
    Tendsto a atTop (𝓝 0) := by
  obtain ⟨s, hs⟩ := h
  have h1 : Tendsto (fun n => partialSum a (n + 1) - partialSum a n) atTop (𝓝 (s - s)) :=
    (hs.comp (tendsto_add_atTop_nat 1)).sub hs
  simp only [sub_self] at h1
  have hx : ∀ n, partialSum a (n + 1) - partialSum a n = a n := by
    intro n; simp [partialSum, Finset.sum_range_succ]
  simpa [hx] using h1

/-- The convergence half of the root test, in the form of Mathlib's `Summable`. -/
private theorem summable_of_limsup_root_lt_one (a : ℕ → ℂ)
    (h : limsup (fun n => ((‖a n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal)) atTop < 1) : Summable a := by
  have h0 : (0 : EReal) ≤ limsup (fun n => ((‖a n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal)) atTop := by
    refine le_limsup_of_frequently_le (Frequently.of_forall fun n => ?_)
    have : (0 : ℝ) ≤ ‖a n‖ ^ ((n : ℝ)⁻¹) := Real.rpow_nonneg (norm_nonneg _) _
    exact_mod_cast this
  obtain ⟨x, hx1, hx2⟩ := exists_between h
  have hxb : x ≠ ⊥ := fun hb => absurd (h0.trans_lt (hb ▸ hx1)) (by simp)
  have hxt : x ≠ ⊤ := fun ht => absurd (ht ▸ hx2) (by simp)
  have hxb' : x = ((x.toReal : ℝ) : EReal) := (EReal.coe_toReal hxt hxb).symm
  set b : ℝ := x.toReal with hbdef
  have hb0 : 0 ≤ b := by
    have h' := h0.trans_lt hx1
    rw [hxb'] at h'
    exact_mod_cast h'.le
  have hb1 : b < 1 := by rw [hxb'] at hx2; exact_mod_cast hx2
  have hev : ∀ᶠ n in atTop, ((‖a n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal) < (b : EReal) := by
    rw [← hxb']; exact eventually_lt_of_limsup_lt hx1
  have key : ∀ᶠ n in atTop, ‖a n‖ ≤ b ^ n := by
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hn' : ‖a n‖ ^ ((n : ℝ)⁻¹) < b := by exact_mod_cast hn
    have hne : n ≠ 0 := by omega
    calc ‖a n‖ = (‖a n‖ ^ ((n : ℝ)⁻¹)) ^ n := (Real.rpow_inv_natCast_pow (norm_nonneg _) hne).symm
      _ ≤ b ^ n := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hn'.le n
  refine Summable.of_norm_bounded_eventually (summable_geometric_of_lt_one hb0 hb1) ?_
  rwa [Nat.cofinite_eq_atTop]

/-- Rudin, Theorem 3.33 (root test): put `α = limsup ‖aₙ‖^{1/n}` in the extended reals.  If
`α < 1` the series `∑ aₙ` converges; if `α > 1` it diverges. -/
theorem solution (a : ℕ → ℂ) :
    (limsup (fun n => ((‖a n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal)) atTop < 1 → Rudin.SeriesConverges a) ∧
    (1 < limsup (fun n => ((‖a n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal)) atTop →
      ¬ Rudin.SeriesConverges a) := by
  refine ⟨fun h => ⟨_, (summable_of_limsup_root_lt_one a h).hasSum.tendsto_sum_nat⟩, ?_⟩
  intro h hconv
  have hz := tendsto_zero_of_seriesConverges hconv
  have hfreq : ∃ᶠ n in atTop, (1 : EReal) < ((‖a n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal) :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) h
  have hev : ∀ᶠ n in atTop, ‖a n‖ < 1 := by
    have hn : Tendsto (fun n => ‖a n‖) atTop (𝓝 0) := by simpa using hz.norm
    exact hn.eventually_lt_const (by norm_num)
  obtain ⟨n, ⟨hn1, hn2⟩, hn3⟩ :=
    ((hfreq.and_eventually hev).and_eventually (eventually_ge_atTop 1)).exists
  have hne : n ≠ 0 := by omega
  have h1 : (1 : ℝ) < ‖a n‖ ^ ((n : ℝ)⁻¹) := by exact_mod_cast hn1
  have h2 : (1 : ℝ) < ‖a n‖ := by
    calc (1 : ℝ) = 1 ^ n := (one_pow n).symm
      _ < (‖a n‖ ^ ((n : ℝ)⁻¹)) ^ n := by
          exact pow_lt_pow_left₀ h1 zero_le_one hne
      _ = ‖a n‖ := Real.rpow_inv_natCast_pow (norm_nonneg _) hne
  linarith

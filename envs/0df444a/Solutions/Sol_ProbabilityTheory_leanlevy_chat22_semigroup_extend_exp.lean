-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat22_semigroup_extend_exp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:05:29.726774+00:00
-- url     : https://prove2.me/submissions/b65b0420-8d58-45a0-812e-458f125a4f73

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

/-- Right-continuity extends the rational-time exponential formula to every
nonnegative real time, as in LeanLevy's fifth factorisation phase. -/
theorem solution
    (φ : ℝ≥0 → ℂ) (c : ℂ)
    (hφ_right : ∀ t, Tendsto φ (𝓝[≥] t) (𝓝 (φ t)))
    (hrat_exp : ∀ (k n : ℕ), 0 < n →
      φ ((k : ℝ≥0) / (n : ℝ≥0)) =
        exp (c * ↑((k : ℝ) / (n : ℝ)))) :
    ∀ t : ℝ≥0, φ t = exp (c * ↑(t : ℝ)) := by
  intro t
  have hf_ge : ∀ m : ℕ, (t : ℝ) ≤
      ↑⌈(t : ℝ) * ↑(m + 1)⌉₊ / ↑(m + 1) :=
    fun m => (le_div_iff₀ (by positivity : (0 : ℝ) < ↑(m + 1))).mpr
      (Nat.le_ceil _)
  have hf_le : ∀ m : ℕ,
      (↑⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ) / ↑(m + 1) ≤
        (t : ℝ) + 1 / ↑(m + 1) :=
    fun m => by
      have hm_pos : (0 : ℝ) < ↑(m + 1) := by positivity
      calc (↑⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ) / ↑(m + 1)
          ≤ ((t : ℝ) * ↑(m + 1) + 1) / ↑(m + 1) :=
            div_le_div_of_nonneg_right
              (Nat.ceil_lt_add_one (by positivity)).le hm_pos.le
        _ = (t : ℝ) + 1 / ↑(m + 1) := by
            rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hm_pos)]
  have hf_tendsto : Tendsto
      (fun m : ℕ => (↑⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ) / ↑(m + 1))
      atTop (𝓝 (t : ℝ)) := by
    have h_upper : Tendsto (fun m : ℕ => (t : ℝ) + 1 / ↑(m + 1))
        atTop (𝓝 (t : ℝ)) := by
      have h0 : Tendsto (fun m : ℕ => (1 : ℝ) / (↑(m + 1) : ℝ))
          atTop (𝓝 0) :=
        (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
          ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
            (tendsto_add_atTop_nat 1))
      have := (tendsto_const_nhds (x := (t : ℝ))).add h0
      rwa [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h_upper hf_ge hf_le
  let g : ℕ → ℝ≥0 := fun m =>
    (⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  have hg_coe : ∀ m, (g m : ℝ) =
      ↑⌈(t : ℝ) * ↑(m + 1)⌉₊ / ↑(m + 1) := fun m => by
    show NNReal.toReal _ = _
    rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
  have hg_ge : ∀ m, t ≤ g m := fun m =>
    NNReal.coe_le_coe.mp (by rw [hg_coe]; exact hf_ge m)
  have hg_real : Tendsto (fun m => (g m : ℝ)) atTop (𝓝 (t : ℝ)) :=
    hf_tendsto.congr (fun m => (hg_coe m).symm)
  have hg_nhds : Tendsto g atTop (𝓝[≥] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨NNReal.tendsto_coe.mp hg_real, Eventually.of_forall fun m => hg_ge m⟩
  have hφ_lim : Tendsto (fun m => φ (g m)) atTop (𝓝 (φ t)) :=
    (hφ_right t).comp hg_nhds
  have hg_eq : ∀ m, φ (g m) = exp (c * ↑(g m : ℝ)) := fun m => by
    rw [hg_coe]
    exact hrat_exp _ _ (by omega)
  have hexp_lim : Tendsto (fun m => exp (c * ↑(g m : ℝ)))
      atTop (𝓝 (exp (c * ↑(t : ℝ)))) :=
    (continuous_exp.tendsto _).comp
      (tendsto_const_nhds.mul
        ((continuous_ofReal.tendsto _).comp hg_real))
  rw [show (fun m => φ (g m)) =
    (fun m => exp (c * ↑(g m : ℝ))) from funext hg_eq] at hφ_lim
  exact tendsto_nhds_unique hφ_lim hexp_lim

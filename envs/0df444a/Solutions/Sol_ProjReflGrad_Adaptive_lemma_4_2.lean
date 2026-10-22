-- Prove2me | solution 1 for ProjReflGrad.Adaptive.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:06:02.408131+00:00
-- url     : https://prove2.me/submissions/ea9d2fee-b208-4305-8ddf-9a8a3a5c9ddb

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

set_option autoImplicit false

open ProjReflGrad.Adaptive in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (F : H → H) (L : ℝ) (hL : 0 < L)
    (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L) (α lamBar : ℝ) (hα : 0 < α) (xn xp yp : H) (taup lamp : ℝ)
    (htaup : 0 ≤ taup) (hlamp : 0 < lamp) (hlampBar : lamp ≤ lamBar) :
    ∃ τ ∈ Set.Ioc (0 : ℝ) 1,
      τ * lamp ≤ stepCap F α lamBar yp taup lamp (xn + τ • (xn - xp)) τ ∧
      ∃ l ∈ Set.Icc (τ * lamp) (stepCap F α lamBar yp taup lamp (xn + τ • (xn - xp)) τ),
        ‖l • F (xn + τ • (xn - xp)) - (τ * lamp) • F yp‖
          ≤ α * ‖(xn + τ • (xn - xp)) - yp‖ := by
  set τ : ℝ := min 1 (α / (L * lamp)) with hτ
  have hτ0 : 0 < τ := lt_min one_pos (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτα : τ * (L * lamp) ≤ α := by
    have : τ ≤ α / (L * lamp) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at this
  set y' : H := xn + τ • (xn - xp) with hy'
  have hcap : τ * lamp ≤ stepCap F α lamBar yp taup lamp y' τ := by
    have h2 : τ * lamp ≤ (1 + taup) / τ * lamp := by
      have : τ ≤ (1 + taup) / τ := by
        rw [le_div_iff₀ hτ0]; nlinarith
      nlinarith
    have h3 : τ * lamp ≤ lamBar := by nlinarith
    unfold stepCap
    split_ifs with hF
    · exact le_min h2 h3
    · refine le_min ?_ (le_min h2 h3)
      have hpos : 0 < ‖F y' - F yp‖ := norm_pos_iff.2 (sub_ne_zero.2 hF)
      have hyy : y' ≠ yp := fun h => hF (by rw [h])
      have hpos2 : 0 < ‖y' - yp‖ := norm_pos_iff.2 (sub_ne_zero.2 hyy)
      rw [le_div_iff₀ hpos]
      have := hC3 y' yp
      nlinarith [mul_pos hτ0 hlamp]
  refine ⟨τ, ⟨hτ0, hτ1⟩, hcap, τ * lamp, ⟨le_refl _, hcap⟩, ?_⟩
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
  have := hC3 y' yp
  have h5 : τ * lamp * ‖F y' - F yp‖ ≤ τ * lamp * (L * ‖y' - yp‖) :=
    mul_le_mul_of_nonneg_left this (by positivity)
  nlinarith [norm_nonneg (y' - yp)]

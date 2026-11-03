-- Prove2me | solution 1 for RegevLWE.GaussConv.pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:56:57.022469+00:00
-- url     : https://prove2.me/submissions/2037a685-ab5c-4fcf-a5ba-fb580585f023

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Theorems.Thm_RegevLWE_GaussConv_eq_11
import Theorems.Thm_RegevLWE_GaussConv_claim_3_8

open RegevLWE.GaussConv

private lemma rhoShiftLattice_eq_rhoCoset_neg {n : ℕ} (α : ℝ)
    (c : EuclideanSpace ℝ (Fin n)) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
    rhoShiftLattice α c L = rhoCoset α L (-c) := by
  unfold rhoShiftLattice rhoCoset rhoShift
  refine tsum_congr fun v => ?_
  rw [sub_eq_add_neg]

private lemma ratio_close_four_eps {A₁ A₂ M₁ M₂ ε : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (h₁ : |A₁ - M₁| ≤ ε * M₁) (h₂ : |A₂ - M₂| ≤ ε * M₂) :
    |A₁ / A₂ - M₁ / M₂| ≤ (M₁ / M₂) * (4 * ε) := by
  have h1_bounds := abs_sub_le_iff.mp h₁
  have h2_bounds := abs_sub_le_iff.mp h₂
  have hA₁_le : A₁ ≤ (1 + ε) * M₁ := by linarith
  have hA₁_ge : (1 - ε) * M₁ ≤ A₁ := by linarith
  have hA₂_le : A₂ ≤ (1 + ε) * M₂ := by linarith
  have hA₂_ge : (1 - ε) * M₂ ≤ A₂ := by linarith
  have h1mε_pos : 0 < 1 - ε := by linarith
  have h1pε_pos : 0 < 1 + ε := by linarith
  have hA₂_pos : 0 < A₂ := mul_pos h1mε_pos hM₂ |>.trans_le hA₂_ge
  have hM₂_ne : M₂ ≠ 0 := hM₂.ne'
  have hA₂_ne : A₂ ≠ 0 := hA₂_pos.ne'
  have hA₁_nonneg : 0 ≤ A₁ := (mul_nonneg h1mε_pos.le hM₁.le).trans hA₁_ge
  rw [abs_le]
  constructor
  · have h_step1 : (1 - ε) * M₁ / ((1 + ε) * M₂) ≤ A₁ / A₂ :=
      div_le_div₀ hA₁_nonneg hA₁_ge hA₂_pos hA₂_le
    have h_step2 : -(M₁ / M₂ * (4 * ε)) ≤ (1 - ε) * M₁ / ((1 + ε) * M₂) - M₁ / M₂ := by
      have h_id : (1 - ε) * M₁ / ((1 + ε) * M₂) - M₁ / M₂ =
          -(M₁ / M₂) * (2 * ε / (1 + ε)) := by
        field_simp
        ring
      rw [h_id]
      have h_le : 2 * ε / (1 + ε) ≤ 4 * ε := by
        rw [div_le_iff₀ h1pε_pos]
        nlinarith
      have hM_div_nonneg : 0 ≤ M₁ / M₂ := div_nonneg hM₁.le hM₂.le
      nlinarith
    linarith
  · have h_step1 : A₁ / A₂ ≤ (1 + ε) * M₁ / ((1 - ε) * M₂) :=
      div_le_div₀ (mul_nonneg h1pε_pos.le hM₁.le) hA₁_le (mul_pos h1mε_pos hM₂) hA₂_ge
    have h_step2 : (1 + ε) * M₁ / ((1 - ε) * M₂) - M₁ / M₂ ≤ M₁ / M₂ * (4 * ε) := by
      have h_id : (1 + ε) * M₁ / ((1 - ε) * M₂) - M₁ / M₂ =
          (M₁ / M₂) * (2 * ε / (1 - ε)) := by
        field_simp
        ring
      rw [h_id]
      have h_le : 2 * ε / (1 - ε) ≤ 4 * ε := by
        rw [div_le_iff₀ h1mε_pos]
        nlinarith
      exact mul_le_mul_of_nonneg_left h_le (div_nonneg hM₁.le hM₂.le)
    linarith

theorem solution {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    [IsZLattice ℝ L] (u : EuclideanSpace ℝ (Fin n)) {r s ε : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (h : smoothingParam L ε ≤ r * s / Real.sqrt (r ^ 2 + s ^ 2))
    (x : EuclideanSpace ℝ (Fin n)) :
    |Ydensity L u r s x - rho (Real.sqrt (r ^ 2 + s ^ 2)) x / Real.sqrt (r ^ 2 + s ^ 2) ^ n| ≤
      rho (Real.sqrt (r ^ 2 + s ^ 2)) x / Real.sqrt (r ^ 2 + s ^ 2) ^ n * (4 * ε) := by
  set t := Real.sqrt (r ^ 2 + s ^ 2)
  set σ := r * s / t
  have ht_pos : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have hσ_pos : 0 < σ := div_pos (mul_pos hr hs) ht_pos
  have hs_le_t : s ≤ t := by
    rw [← Real.sqrt_sq hs.le]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hσ_le_r : σ ≤ r := by
    dsimp [σ]
    rw [div_le_iff₀ ht_pos]
    exact mul_le_mul_of_nonneg_left hs_le_t hr.le
  have hr_sp : smoothingParam L ε ≤ r := h.trans hσ_le_r
  set c₁ := (r / t) ^ 2 • x - u
  set D := (ZLattice.covolume L)⁻¹
  have hD_pos : 0 < D := inv_pos.mpr (ZLattice.covolume_pos L MeasureTheory.volume)
  set M₁ := σ ^ n * D
  set M₂ := r ^ n * D
  have hM₁_pos : 0 < M₁ := mul_pos (pow_pos hσ_pos n) hD_pos
  have hM₂_pos : 0 < M₂ := mul_pos (pow_pos hr n) hD_pos
  have h_bound1 : |rhoShiftLattice σ c₁ L - M₁| ≤ ε * M₁ := by
    rw [rhoShiftLattice_eq_rhoCoset_neg]
    exact claim_3_8 L (-c₁) hε hσ_pos h
  have h_bound2 : |rhoShiftLattice r (-u) L - M₂| ≤ ε * M₂ := by
    rw [rhoShiftLattice_eq_rhoCoset_neg, neg_neg]
    exact claim_3_8 L u hε hr hr_sp
  have h_ratio := ratio_close_four_eps hM₁_pos hM₂_pos hε hε2 h_bound1 h_bound2
  have h_M_ratio : (1 / s ^ n * rho t x) * (M₁ / M₂) = rho t x / t ^ n := by
    dsimp [M₁, M₂, σ]
    have hr_ne : r ^ n ≠ 0 := (pow_pos hr n).ne'
    have hs_ne : s ^ n ≠ 0 := (pow_pos hs n).ne'
    have ht_ne : t ^ n ≠ 0 := (pow_pos ht_pos n).ne'
    have hD_ne : D ≠ 0 := hD_pos.ne'
    rw [div_pow, mul_pow]
    field_simp
  rw [eq_11 L u x hr hs]
  change |1 / s ^ n * rho t x * (rhoShiftLattice σ c₁ L / rhoShiftLattice r (-u) L) -
      rho t x / t ^ n| ≤ rho t x / t ^ n * (4 * ε)
  rw [← h_M_ratio, ← mul_sub]
  have h_pre_nonneg : 0 ≤ 1 / s ^ n * rho t x := by
    unfold rho
    positivity
  calc |(1 / s ^ n * rho t x) * (rhoShiftLattice σ c₁ L / rhoShiftLattice r (-u) L - M₁ / M₂)|
      = (1 / s ^ n * rho t x) * |rhoShiftLattice σ c₁ L / rhoShiftLattice r (-u) L - M₁ / M₂| := by
        rw [abs_mul, abs_of_nonneg h_pre_nonneg]
    _ ≤ (1 / s ^ n * rho t x) * (M₁ / M₂ * (4 * ε)) :=
        mul_le_mul_of_nonneg_left h_ratio h_pre_nonneg
    _ = (1 / s ^ n * rho t x) * (M₁ / M₂) * (4 * ε) := by ring

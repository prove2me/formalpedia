-- Prove2me | solution 1 for WrightPDIPM.Potential.eq_4_26_4_27
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:47:58.479372+00:00
-- url     : https://prove2.me/submissions/349761ab-22b3-4ae3-b1bb-77338b2163cb

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting
open Matrix
open WrightPDIPM.Potential

theorem g69b_dxds0 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (h1 : Aᵀ *ᵥ dlam + ds = 0) (h2 : A *ᵥ dx = 0) : dx ⬝ᵥ ds = 0 := by
  have : ds = -(Aᵀ *ᵥ dlam) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h1
  rw [this, dotProduct_neg, dotProduct_mulVec, vecMul_transpose, h2]
  simp

theorem g69b_rvec_sq {n : ℕ} (ρ : ℝ) (x s : Fin n → ℝ) (i : Fin n) (hw : 0 < x i * s i) :
    rvec ρ x s i ^ 2 = (-(x i * s i) + (n : ℝ) / ρ * mu x s) ^ 2 / (x i * s i) := by
  unfold rvec vvec
  have hv := Real.sqrt_pos.mpr hw
  have hv2 := Real.sq_sqrt hw.le
  set v := Real.sqrt (x i * s i)
  rw [← hv2]
  field_simp
  try ring

theorem solution {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ)
    (hF : (x, lam, s) ∈ Fo A b c) (ρ : ℝ) (hρ : (n : ℝ) < ρ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hdir : IsPRDirection A ρ x s dx dlam ds)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    g2 τ x s dx ds ≤ 1 / (1 - τ) * (norm2 (rvec ρ x s) ^ 2 / vmin x s ^ 2) ∧
      g1 ρ x s dx ds = -(ρ / (n * mu x s)) * norm2 (rvec ρ x s) ^ 2 := by
  obtain ⟨_, _, hx, hs⟩ := hF
  simp only at hx hs
  obtain ⟨⟨hAdx, hAds⟩, h3⟩ := hdir
  have hdxds := g69b_dxds0 A dx dlam ds hAds hAdx
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ0 : 0 < ρ := lt_trans hn' hρ
  have hw : ∀ i, 0 < x i * s i := fun i => mul_pos (hx i) (hs i)
  have hxs : 0 < x ⬝ᵥ s :=
    Finset.sum_pos (fun i _ => hw i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hmu : 0 < mu x s := div_pos hxs hn'
  have hxsmu : x ⬝ᵥ s = n * mu x s := by unfold mu; field_simp
  set σ := (n : ℝ) / ρ with hσ
  set μ := mu x s
  have hr2 : norm2 (rvec ρ x s) ^ 2 = ∑ i, (-(x i * s i) + σ * μ) ^ 2 / (x i * s i) := by
    unfold norm2
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    exact Finset.sum_congr rfl (fun i _ => g69b_rvec_sq ρ x s i (hw i))
  constructor
  · -- g2 bound
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := vvec x s)
    have hvmin_pos : 0 < vmin x s := by
      unfold vmin; rw [← hj]; exact Real.sqrt_pos.mpr (hw j)
    have hvmin_le : ∀ i, vmin x s ^ 2 ≤ x i * s i := by
      intro i
      have h1 : vmin x s ≤ vvec x s i := ciInf_le (Finite.bddBelow_range _) i
      have h2 : vvec x s i ^ 2 = x i * s i := Real.sq_sqrt (hw i).le
      rw [← h2]
      exact pow_le_pow_left₀ hvmin_pos.le h1 2
    set p : Fin n → ℝ := fun i => dx i ^ 2 * s i / x i + ds i ^ 2 * x i / s i
    have hp0 : ∀ i, 0 ≤ p i := by
      intro i; have := hx i; have := hs i; simp only [p]; positivity
    have hpi : ∀ i, (dx i / x i) ^ 2 + (ds i / s i) ^ 2 = p i / (x i * s i) := by
      intro i
      simp only [p]
      field_simp [(hx i).ne', (hs i).ne']
      try ring
    have hpsum : ∑ i, p i = ∑ i, (-(x i * s i) + σ * μ) ^ 2 / (x i * s i) := by
      have : ∀ i, (-(x i * s i) + σ * μ) ^ 2 / (x i * s i) = p i + 2 * (dx i * ds i) := by
        intro i
        rw [← h3 i]
        simp only [p]
        field_simp [(hx i).ne', (hs i).ne']
        ring
      have hsplit : ∑ i, (-(x i * s i) + σ * μ) ^ 2 / (x i * s i) =
          ∑ i, p i + 2 * (dx ⬝ᵥ ds) := by
        rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
      rw [hsplit, hdxds]; ring
    have hkey : norm2 (fun i => dx i / x i) ^ 2 + norm2 (fun i => ds i / s i) ^ 2 ≤
        norm2 (rvec ρ x s) ^ 2 / vmin x s ^ 2 := by
      unfold norm2
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      rw [← norm2, hr2, ← hpsum, ← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_le_sum
      intro i _
      rw [hpi]
      exact div_le_div_of_nonneg_left (hp0 i) (by positivity) (hvmin_le i)
    unfold g2
    exact mul_le_mul_of_nonneg_left hkey (le_of_lt (one_div_pos.mpr (by linarith)))
  · -- g1 identity
    have hsum1 : s ⬝ᵥ dx + x ⬝ᵥ ds = -(n * μ) + n * (σ * μ) := by
      have : s ⬝ᵥ dx + x ⬝ᵥ ds = ∑ i, (-(x i * s i) + σ * μ) := by
        unfold dotProduct
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => h3 i)
      rw [this, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← hxsmu]; rfl
    have hsum2 : ∑ i, (dx i / x i + ds i / s i) = ∑ i, (-1 + σ * μ * (1 / (x i * s i))) := by
      apply Finset.sum_congr rfl
      intro i _
      have := h3 i
      field_simp [(hx i).ne', (hs i).ne']
      linear_combination this
    have hsum3 : ∑ i, (-(x i * s i) + σ * μ) ^ 2 / (x i * s i) =
        ∑ i, (x i * s i - 2 * σ * μ + (σ * μ) ^ 2 * (1 / (x i * s i))) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(hx i).ne', (hs i).ne']
      ring
    set S := ∑ i, 1 / (x i * s i)
    have T1 : ∑ i, (-1 + σ * μ * (1 / (x i * s i))) = -(n : ℝ) + σ * μ * S := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have T2 : ∑ i, (x i * s i - 2 * σ * μ + (σ * μ) ^ 2 * (1 / (x i * s i))) =
        n * μ - n * (2 * σ * μ) + (σ * μ) ^ 2 * S := by
      have e : ∑ i, x i * s i = n * μ := hxsmu
      simp only [S, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, e,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold g1
    rw [hr2, hsum1, hsum2, hsum3, hxsmu, T1, T2, hσ]
    field_simp
    ring

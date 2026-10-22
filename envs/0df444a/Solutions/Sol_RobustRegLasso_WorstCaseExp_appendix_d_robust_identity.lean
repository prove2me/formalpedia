-- Prove2me | solution 1 for RobustRegLasso.WorstCaseExp.appendix_d_robust_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:46:21.056523+00:00
-- url     : https://prove2.me/submissions/d603e5b8-a24c-466e-a091-38e599c0c2cc

import Mathlib
import Definitions.Def_RobustRegLasso_WorstCaseExp_Basic

set_option autoImplicit false
open RobustRegLasso.WorstCaseExp

noncomputable def rrw_e (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap

theorem rrw_l2 {n : ℕ} (v : Fin n → ℝ) : l2norm v = ‖rrw_e n v‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [l2norm, rrw_e, Real.norm_eq_abs, sq_abs]

theorem rrw_add {n : ℕ} (u v : Fin n → ℝ) : l2norm (u + v) ≤ l2norm u + l2norm v := by
  rw [rrw_l2, rrw_l2, rrw_l2, map_add]; exact norm_add_le _ _

theorem rrw_smul {n : ℕ} (c : ℝ) (v : Fin n → ℝ) : l2norm (c • v) = |c| * l2norm v := by
  rw [rrw_l2, rrw_l2, map_smul, norm_smul, Real.norm_eq_abs]

theorem rrw_neg {n : ℕ} (v : Fin n → ℝ) : l2norm (-v) = l2norm v := by
  have := rrw_smul (n := n) (-1) v
  simpa using this

theorem rrw_sum {n m : ℕ} (f : Fin m → Fin n → ℝ) : l2norm (∑ j, f j) ≤ ∑ j, l2norm (f j) := by
  rw [rrw_l2, map_sum]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun j _ => (rrw_l2 _).symm

theorem rrw_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ l2norm v := Real.sqrt_nonneg _

theorem l1nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ l1norm x := Finset.sum_nonneg fun j _ => abs_nonneg _

theorem solution {n m : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) (x : Fin m → ℝ) :
    IsGreatest
      {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
        Admissible c σ Δ ∧ v = l2norm (b + σ - Matrix.mulVec (A + Δ) x)}
      (regularizedLoss A b c x) := by
  set s : ℝ := Real.sqrt n * c with hs
  have hs0 : 0 ≤ s := mul_nonneg (Real.sqrt_nonneg _) hc
  set r : Fin n → ℝ := b - Matrix.mulVec A x with hr
  set ρ : ℝ := l2norm r with hρ
  refine ⟨?_, ?_⟩
  · -- attained
    obtain ⟨u, hu1, hru⟩ : ∃ u : Fin n → ℝ, l2norm u = 1 ∧ r = ρ • u := by
      by_cases h0 : ρ = 0
      · refine ⟨Pi.single ⟨0, hn⟩ 1, ?_, ?_⟩
        · simp [l2norm, Pi.single_apply, ite_pow]
        · have : r = 0 := by
            funext i
            have h1 : ∑ i, r i ^ 2 = 0 := by
              have := Real.sqrt_eq_zero'.mp h0
              exact le_antisymm this (Finset.sum_nonneg fun i _ => sq_nonneg _)
            have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (r i))).mp h1 i (Finset.mem_univ i)
            simpa using this
          rw [h0, this]; simp
      · refine ⟨ρ⁻¹ • r, ?_, ?_⟩
        · rw [rrw_smul, abs_of_pos (inv_pos.mpr (lt_of_le_of_ne (rrw_nonneg r) (Ne.symm h0)))]
          field_simp
          exact div_self h0
        · rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
    set D : Matrix (Fin n) (Fin m) ℝ := fun i j => -(s * Real.sign (x j)) * u i with hD
    refine ⟨s • u, D, ⟨?_, ?_⟩, ?_⟩
    · rw [rrw_smul, hu1, abs_of_nonneg hs0]; simpa using hs.le
    · intro j
      have : (fun i => D i j) = (-(s * Real.sign (x j))) • u := rfl
      rw [this, rrw_smul, hu1, abs_neg, abs_mul, abs_of_nonneg hs0]
      have : |Real.sign (x j)| ≤ 1 := by
        rcases lt_trichotomy (x j) 0 with h | h | h
        · rw [Real.sign_of_neg h]; simp
        · simp [h]
        · rw [Real.sign_of_pos h]; simp
      nlinarith
    · have hsign : ∀ j, Real.sign (x j) * x j = |x j| := fun j => by
        rcases lt_trichotomy (x j) 0 with h | h | h
        · rw [Real.sign_of_neg h, abs_of_neg h]; ring
        · simp [h]
        · rw [Real.sign_of_pos h, abs_of_pos h]; ring
      have key : b + s • u - Matrix.mulVec (A + D) x = (ρ + s + s * l1norm x) • u := by
        funext i
        have h1 : b i - A.mulVec x i = ρ * u i := by
          have := congrFun hru i
          simpa [hr] using this
        have hd : Matrix.mulVec D x i = -(s * l1norm x) * u i := by
          simp only [hD, Matrix.mulVec, dotProduct, l1norm, Finset.mul_sum, Finset.sum_mul,
            neg_mul]
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← hsign j]; ring
        simp only [Matrix.add_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hd]
        linarith
      rw [key, rrw_smul, hu1, abs_of_nonneg (by have := rrw_nonneg r; have := l1nonneg x; positivity)]
      simp only [regularizedLoss, hs, hρ, hr]
      ring
  · rintro v ⟨σ, Δ, ⟨hσ, hΔ⟩, rfl⟩
    have hdec : b + σ - Matrix.mulVec (A + Δ) x = r + σ + -(∑ j, x j • (fun i => Δ i j)) := by
      funext i
      simp only [hr, Matrix.add_mulVec, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_congr rfl fun j _ => mul_comm (x j) (Δ i j)]
      ring
    have h1 : l2norm (∑ j, x j • (fun i => Δ i j)) ≤ s * l1norm x := by
      refine (rrw_sum _).trans ?_
      rw [l1norm, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [rrw_smul]
      have := hΔ j
      nlinarith [abs_nonneg (x j), rrw_nonneg (fun i => Δ i j)]
    calc l2norm (b + σ - Matrix.mulVec (A + Δ) x)
        = l2norm (r + σ + -(∑ j, x j • (fun i => Δ i j))) := by rw [hdec]
      _ ≤ l2norm (r + σ) + l2norm (-(∑ j, x j • (fun i => Δ i j))) := rrw_add _ _
      _ ≤ (l2norm r + l2norm σ) + l2norm (∑ j, x j • (fun i => Δ i j)) := by
          rw [rrw_neg]; linarith [rrw_add r σ]
      _ ≤ regularizedLoss A b c x := by
          simp only [regularizedLoss, hρ.symm]
          have : l2norm σ ≤ s := hσ
          simp only [hs] at *
          nlinarith [h1]

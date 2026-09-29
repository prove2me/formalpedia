-- Prove2me | solution 1 for VectorSpaceOpt.gauss_markov_trace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T13:52:05.253639+00:00
-- url     : https://prove2.me/submissions/33bcd905-cdfb-44bf-8d7c-ed0fd7246f5c

import Mathlib
open Matrix


theorem solution {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosDef)
    (hW : LinearIndependent ℝ (fun j : Fin n => fun i : Fin m => W i j))
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = (Wᵀ * Q⁻¹ * W)⁻¹ * Wᵀ * Q⁻¹) :
    K₀ * W = 1 ∧
    (∀ K : Matrix (Fin n) (Fin m) ℝ, K * W = 1 →
      ∀ i, (K₀ * Q * K₀ᵀ) i i ≤ (K * Q * Kᵀ) i i) ∧
    K₀ * Q * K₀ᵀ = (Wᵀ * Q⁻¹ * W)⁻¹ := by
  classical
  have hQu : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.isUnit
  have hQi : (Q⁻¹).PosDef := Matrix.posDef_inv_iff.2 hQ
  have hinj : ∀ x : Fin n → ℝ, W.mulVec x = 0 → x = 0 := by
    intro x hx
    funext j
    refine (Fintype.linearIndependent_iff.1 hW) x ?_ j
    funext i
    have hi : W.mulVec x i = 0 := congrFun hx i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hi]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hWinj : Function.Injective W.mulVec := by
    intro a b hab
    have h : W.mulVec (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    exact sub_eq_zero.1 (hinj _ h)
  set M : Matrix (Fin n) (Fin n) ℝ := Wᵀ * Q⁻¹ * W with hM
  have hMpd : M.PosDef := by
    have h := hQi.conjTranspose_mul_mul_same hWinj
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rwa [hM]
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1 hMpd.isUnit
  have hQsymm : Qᵀ = Q := by
    have h : Qᴴ = Q := hQ.isHermitian
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hQisymm : (Q⁻¹)ᵀ = Q⁻¹ := by rw [Matrix.transpose_nonsing_inv, hQsymm]
  have hMsymm : Mᵀ = M := by
    rw [hM, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hQisymm]
    simp only [Matrix.mul_assoc]
  have hMisymm : (M⁻¹)ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hMsymm]
  have hMM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hMu
  have hQQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQu
  have hQQ' : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQu
  have hunb : K₀ * W = 1 := by
    rw [hK₀]
    simp only [Matrix.mul_assoc]
    rw [show Wᵀ * (Q⁻¹ * W) = M by rw [hM]; simp only [Matrix.mul_assoc]]
    exact hMM
  have hK₀T : K₀ᵀ = Q⁻¹ * W * M⁻¹ := by
    rw [hK₀, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hQisymm, hMisymm]
    simp only [Matrix.mul_assoc]
  have hcov : K₀ * Q * K₀ᵀ = M⁻¹ := by
    rw [hK₀T, hK₀]
    simp only [Matrix.mul_assoc]
    rw [show Q⁻¹ * (Q * (Q⁻¹ * (W * M⁻¹))) = Q⁻¹ * (W * M⁻¹) by
      rw [← Matrix.mul_assoc Q⁻¹ Q, hQQ, Matrix.one_mul]]
    rw [show M⁻¹ * (Wᵀ * (Q⁻¹ * (W * M⁻¹))) = M⁻¹ * (M * M⁻¹) by
      rw [hM]; simp only [Matrix.mul_assoc]]
    rw [← Matrix.mul_assoc, hMM, Matrix.one_mul]
  refine ⟨hunb, ?_, by rw [hcov, hM]⟩
  intro K hK i
  obtain ⟨D, hDdef⟩ : ∃ D : Matrix (Fin n) (Fin m) ℝ, D = K - K₀ := ⟨_, rfl⟩
  have hDW : D * W = 0 := by rw [hDdef, Matrix.sub_mul, hK, hunb, sub_self]
  have hA : K₀ * Q * Dᵀ = 0 := by
    rw [hK₀]
    simp only [Matrix.mul_assoc]
    rw [show Q⁻¹ * (Q * Dᵀ) = Dᵀ by rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul]]
    rw [show Wᵀ * Dᵀ = (D * W)ᵀ by rw [Matrix.transpose_mul]]
    rw [hDW, Matrix.transpose_zero, Matrix.mul_zero]
  have hB : D * Q * K₀ᵀ = 0 := by
    rw [hK₀T]
    simp only [Matrix.mul_assoc]
    rw [show Q * (Q⁻¹ * (W * M⁻¹)) = W * M⁻¹ by
      rw [← Matrix.mul_assoc Q Q⁻¹, hQQ', Matrix.one_mul]]
    rw [← Matrix.mul_assoc, hDW, Matrix.zero_mul]
  have hexpand : K * Q * Kᵀ = K₀ * Q * K₀ᵀ + D * Q * Dᵀ := by
    have e : K₀ * Q * K₀ᵀ + D * Q * Dᵀ
        = K * Q * Kᵀ - K₀ * Q * Dᵀ - D * Q * K₀ᵀ := by
      rw [hDdef]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_sub]
      abel
    rw [e, hA, hB, sub_zero, sub_zero]
  have hpsd : (D * Q * Dᵀ).PosSemidef := by
    have h := hQ.posSemidef.mul_mul_conjTranspose_same D
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [hexpand]
  simp only [Matrix.add_apply]
  linarith [hpsd.diag_nonneg (i := i)]

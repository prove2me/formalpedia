-- Prove2me | solution 1 for PhaseCut.Tight.eq15_iff_eq16
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:49:05.550994+00:00
-- url     : https://prove2.me/submissions/685b8faf-bb41-4ee2-aaf6-feba34f2fba8

import Mathlib
import Definitions.Def_PhaseCut_Tight_Defs
set_option autoImplicit false
open Matrix PhaseCut.Tight
open scoped ComplexOrder MatrixOrder

theorem EE_pinv_mul {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ)
    (hA : Function.Injective A.mulVec) : pinv A * A = 1 := by
  have h1 : (Aᴴ * A).PosDef := Matrix.PosDef.conjTranspose_mul_self A hA
  have h2 : IsUnit (Aᴴ * A).det := (Matrix.isUnit_iff_isUnit_det _).1 h1.isUnit
  unfold pinv
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h2]

theorem EE_D_Dinv {n : ℕ} (b : Fin n → ℝ) (hb : ∀ i, b i ≠ 0) : D b * Dinv b = 1 := by
  unfold D Dinv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have : (b i : ℂ) ≠ 0 := by exact_mod_cast hb i
  simp [this]

theorem EE_Dinv_D {n : ℕ} (b : Fin n → ℝ) (hb : ∀ i, b i ≠ 0) : Dinv b * D b = 1 := by
  unfold D Dinv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have : (b i : ℂ) ≠ 0 := by exact_mod_cast hb i
  simp [this]

theorem EE_Dh {n : ℕ} (b : Fin n → ℝ) : (D b)ᴴ = D b := by
  unfold D
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

theorem EE_Dinvh {n : ℕ} (b : Fin n → ℝ) : (Dinv b)ᴴ = Dinv b := by
  unfold Dinv
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

theorem EE_Qh {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) : (A * pinv A)ᴴ = A * pinv A := by
  unfold pinv
  simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]

theorem EE_QQ {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ)
    (hA : Function.Injective A.mulVec) : (A * pinv A) * (A * pinv A) = A * pinv A := by
  have hP := EE_pinv_mul A hA
  calc (A * pinv A) * (A * pinv A) = A * (pinv A * A) * pinv A := by simp only [Matrix.mul_assoc]
    _ = A * pinv A := by rw [hP]; simp

theorem EE_PA {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ)
    (hA : Function.Injective A.mulVec) : (1 - A * pinv A) * A = 0 := by
  have hP := EE_pinv_mul A hA
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hP, Matrix.mul_one, sub_self]

theorem EE_Mpsd {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) :
    (Mmat A b).PosSemidef := by
  have hQ := EE_QQ A hA
  set P : Matrix (Fin n) (Fin n) ℂ := 1 - A * pinv A with hPdef
  have hPh : Pᴴ = P := by
    rw [hPdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, EE_Qh]
  have hPP : P * P = P := by
    rw [hPdef]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQ, Matrix.one_mul]
    abel
  have : Mmat A b = (P * D b)ᴴ * (P * D b) := by
    rw [Matrix.conjTranspose_mul, hPh, EE_Dh]
    unfold Mmat
    rw [← hPdef]
    calc D b * P * D b = D b * (P * P) * D b := by rw [hPP]
      _ = D b * P * (P * D b) := by simp only [Matrix.mul_assoc]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem EE_mulzero {m : ℕ} (U M : Matrix (Fin m) (Fin m) ℂ)
    (hU : U.PosSemidef) (hM : M.PosSemidef) (h : (U * M).trace = 0) :
    U * M = 0 := by
  obtain ⟨W, hW⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hU.nonneg
  obtain ⟨N, hN⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have hW' : U = Wᴴ * W := hW
  have hN' : M = Nᴴ * N := hN
  have h1 : ((W * Nᴴ) * (W * Nᴴ)ᴴ).trace = 0 := by
    have : ((W * Nᴴ) * (W * Nᴴ)ᴴ).trace = (U * M).trace := by
      rw [hW', hN', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [Matrix.trace_mul_comm (Wᴴ * W)]
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [this, h]
  have h2 : W * Nᴴ = 0 := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.1 h1
  rw [hW', hN']
  calc Wᴴ * W * (Nᴴ * N) = Wᴴ * (W * Nᴴ) * N := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h2]; simp

theorem EE_Mphi {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0) (X : Matrix (Fin p) (Fin p) ℂ) :
    Mmat A b * Phi A b X = 0 := by
  have hD := EE_D_Dinv b hb
  have hPA := EE_PA A hA
  unfold Mmat Phi
  calc D b * (1 - A * pinv A) * D b * (Dinv b * A * X * Aᴴ * Dinv b)
      = D b * (1 - A * pinv A) * (D b * Dinv b) * A * X * Aᴴ * Dinv b := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hD, Matrix.mul_one]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (1 - A * pinv A), hPA]; simp

theorem EE_Phi_psd {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (X : Matrix (Fin p) (Fin p) ℂ) (hX : X.PosSemidef) : (Phi A b X).PosSemidef := by
  have := hX.mul_mul_conjTranspose_same (Dinv b * A)
  have e : Phi A b X = Dinv b * A * X * (Dinv b * A)ᴴ := by
    unfold Phi
    rw [Matrix.conjTranspose_mul, EE_Dinvh]
    simp only [Matrix.mul_assoc]
  rw [e]; exact this

theorem EE_eq15 {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0) :
    ∀ U : Matrix (Fin n) (Fin n) ℂ,
      ((Mmat A b * U).trace = 0 ∧ U.PosSemidef) ↔
        ∃ X : Matrix (Fin p) (Fin p) ℂ, X.PosSemidef ∧ U = Phi A b X := by
  intro U
  have hD := EE_D_Dinv b hb
  have hDi := EE_Dinv_D b hb
  have hPs := EE_pinv_mul A hA
  constructor
  · rintro ⟨htr, hU⟩
    have hM := EE_Mpsd A b hA
    have h0 : U * Mmat A b = 0 := by
      apply EE_mulzero U _ hU hM
      rw [Matrix.trace_mul_comm]; exact htr
    -- V = D U D
    set P : Matrix (Fin n) (Fin n) ℂ := 1 - A * pinv A with hPdef
    have h1 : U * D b * P = 0 := by
      have : U * (D b * P * D b) * Dinv b = 0 := by
        have : U * (D b * P * D b) = 0 := h0
        rw [this]; simp
      calc U * D b * P = U * (D b * P * D b) * Dinv b := by
            simp only [Matrix.mul_assoc]
            rw [hD]; simp
        _ = 0 := this
    set V : Matrix (Fin n) (Fin n) ℂ := D b * U * D b with hV
    have hVpsd : V.PosSemidef := by
      have := hU.mul_mul_conjTranspose_same (D b)
      rwa [EE_Dh] at this
    have hVh : Vᴴ = V := hVpsd.1
    have hVP : V * P = 0 := by
      rw [hV, Matrix.mul_assoc, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U (D b) P, h1]; simp
    have hVQ : V * (A * pinv A) = V := by
      have : V * (1 - A * pinv A) = 0 := hVP
      rw [Matrix.mul_sub, Matrix.mul_one] at this
      exact (sub_eq_zero.1 this).symm
    have hQV : (A * pinv A) * V = V := by
      have := congrArg Matrix.conjTranspose hVQ
      rw [Matrix.conjTranspose_mul, EE_Qh, hVh] at this
      exact this
    refine ⟨pinv A * V * (pinv A)ᴴ, ?_, ?_⟩
    · have := hVpsd.mul_mul_conjTranspose_same (pinv A)
      exact this
    · have e1 : A * (pinv A * V * (pinv A)ᴴ) * Aᴴ = V := by
        calc A * (pinv A * V * (pinv A)ᴴ) * Aᴴ
            = (A * pinv A) * V * (A * pinv A)ᴴ := by
              rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
          _ = V := by rw [EE_Qh, hQV, hVQ]
      have : Phi A b (pinv A * V * (pinv A)ᴴ) = Dinv b * V * Dinv b := by
        unfold Phi
        calc Dinv b * A * (pinv A * V * (pinv A)ᴴ) * Aᴴ * Dinv b
            = Dinv b * (A * (pinv A * V * (pinv A)ᴴ) * Aᴴ) * Dinv b := by simp only [Matrix.mul_assoc]
          _ = Dinv b * V * Dinv b := by rw [e1]
      rw [this, hV]
      calc U = (Dinv b * D b) * U * (D b * Dinv b) := by rw [hDi, hD]; simp
        _ = Dinv b * (D b * U * D b) * Dinv b := by simp only [Matrix.mul_assoc]
  · rintro ⟨X, hX, rfl⟩
    refine ⟨?_, EE_Phi_psd A b X hX⟩
    rw [EE_Mphi A b hA hb X]; simp

theorem solution {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0) (hsol : IsSolvable A b) :
    ∀ U : Matrix (Fin n) (Fin n) ℂ,
      ((Mmat A b * U).trace = 0 ∧ U.PosSemidef) ↔
        ∃ X : Matrix (Fin p) (Fin p) ℂ, X.PosSemidef ∧ U = Phi A b X :=
  EE_eq15 A b hA hb

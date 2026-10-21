-- Prove2me | solution 1 for ParamSDO.Transition.optimality_conditions_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:25:53.747694+00:00
-- url     : https://prove2.me/submissions/adf3006e-58b4-4ada-b62f-2ad83217536b

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

open ParamSDO.Transition Matrix MatrixOrder

lemma psdo_trace_mul_psd {n : ℕ} {S X : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    (hX : X.PosSemidef) : 0 ≤ (S * X).trace ∧ ((S * X).trace = 0 → X * S = 0) := by
  obtain ⟨G, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hS.nonneg
  obtain ⟨H, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  simp only [star_eq_conjTranspose]
  have htr : (Gᴴ * G * (Hᴴ * H)).trace = ((G * Hᴴ) * (G * Hᴴ)ᴴ).trace := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [show Gᴴ * G * (Hᴴ * H) = Gᴴ * (G * Hᴴ * H) by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [htr]
  refine ⟨(posSemidef_self_mul_conjTranspose (G * Hᴴ)).trace_nonneg, fun h0 => ?_⟩
  have hz : G * Hᴴ = 0 := trace_mul_conjTranspose_self_eq_zero_iff.1 h0
  have hz' : H * Gᴴ = 0 := by
    have := congrArg conjTranspose hz
    simpa [conjTranspose_mul] using this
  calc Hᴴ * H * (Gᴴ * G) = Hᴴ * (H * Gᴴ) * G := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hz']; simp

lemma psdo_pair_split {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵ : ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin m → ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (hX : X ∈ Pfeas A b)
    (hD : (y, S) ∈ Dfeas A C Cbar ϵ) :
    pair (C + ϵ • Cbar) X = b ⬝ᵥ y + (S * X).trace := by
  unfold pair
  rw [← hD.1]
  simp only [Matrix.add_mul, Matrix.sum_mul, Matrix.trace_add, Matrix.trace_sum,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hX.2 i
  unfold pair at this
  rw [this, mul_comm]

theorem solution {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    ∀ ϵ ∈ interior (domE A b C Cbar), ∀ (X : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ)
      (S : Matrix (Fin n) (Fin n) ℝ),
      (X ∈ Pstar A b C Cbar ϵ ∧ (y, S) ∈ Dstar A b C Cbar ϵ) ↔
        (X ∈ Pfeas A b ∧ (y, S) ∈ Dfeas A C Cbar ϵ ∧ X * S = 0) := by
  intro ϵ _ X y S
  constructor
  · rintro ⟨⟨hXf, hXv⟩, ⟨hDf, hDv⟩⟩
    refine ⟨hXf, hDf, ?_⟩
    have heq : pair (C + ϵ • Cbar) X = b ⬝ᵥ y := by
      exact_mod_cast hXv.trans hDv.symm
    rw [psdo_pair_split A b C Cbar ϵ X y S hXf hDf] at heq
    exact (psdo_trace_mul_psd hDf.2 hXf.1).2 (by linarith)
  · rintro ⟨hXf, hDf, hXS⟩
    have htr : (S * X).trace = 0 := by rw [Matrix.trace_mul_comm, hXS, Matrix.trace_zero]
    have hval : pair (C + ϵ • Cbar) X = b ⬝ᵥ y := by
      rw [psdo_pair_split A b C Cbar ϵ X y S hXf hDf, htr, add_zero]
    have hv : v A b C Cbar ϵ = ((b ⬝ᵥ y : ℝ) : EReal) := by
      apply le_antisymm
      · rw [← hval]; exact iInf₂_le X hXf
      · refine le_iInf₂ fun X' hX' => ?_
        rw [psdo_pair_split A b C Cbar ϵ X' y S hX' hDf]
        exact_mod_cast le_add_of_nonneg_right (psdo_trace_mul_psd hDf.2 hX'.1).1
    exact ⟨⟨hXf, by rw [hv, hval]⟩, ⟨hDf, hv.symm⟩⟩

-- Prove2me | solution 1 for TroppMatrixConcentration.ch8_perspective_convex
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:48:27.453978+00:00
-- url     : https://prove2.me/submissions/8c4fa7e1-8fa2-4ad0-bde2-2210af7383d4

import Theorems.Thm_TroppMatrixConcentration_ch8_operator_jensen
import Theorems.Thm_TroppMatrixConcentration_ch8_perspective_sqrt_normalization
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

open TroppMatrixConcentration

theorem solution {d : ℕ} [NeZero d]
    (f : ℝ → ℝ) (hf : ch8_operatorConvexOn (Set.Ioi 0) f)
    (A₁ A₂ H₁ H₂ : Matrix (Fin d) (Fin d) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hH₁ : H₁.PosDef) (hH₂ : H₂.PosDef)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    loewnerLE
      (ch8_perspective f (t • A₁ + (1 - t) • A₂) (t • H₁ + (1 - t) • H₂))
      (t • ch8_perspective f A₁ H₁ + (1 - t) • ch8_perspective f A₂ H₂) := by
  have htbar : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  let A := t • A₁ + (1 - t) • A₂
  have hA : A.PosDef := by
    by_cases ht : t = 0
    · simpa [A, ht] using hA₂
    · exact (hA₁.smul (lt_of_le_of_ne ht₀ (Ne.symm ht))).add_posSemidef
        (hA₂.posSemidef.smul htbar)
  let S := ch8_matrixFunction Real.sqrt A
  let R := ch8_matrixFunction (fun x => (Real.sqrt x)⁻¹) A
  let S₁ := ch8_matrixFunction Real.sqrt A₁
  let R₁ := ch8_matrixFunction (fun x => (Real.sqrt x)⁻¹) A₁
  let S₂ := ch8_matrixFunction Real.sqrt A₂
  let R₂ := ch8_matrixFunction (fun x => (Real.sqrt x)⁻¹) A₂
  obtain ⟨hS, hR, hSS, hRS, hSR⟩ := ch8_perspective_sqrt_normalization A hA
  obtain ⟨hS₁, hR₁, hSS₁, hRS₁, hSR₁⟩ := ch8_perspective_sqrt_normalization A₁ hA₁
  obtain ⟨hS₂, hR₂, hSS₂, hRS₂, hSR₂⟩ := ch8_perspective_sqrt_normalization A₂ hA₂
  change S.IsHermitian at hS
  change R.IsHermitian at hR
  change S * S = A at hSS
  change R * S = 1 at hRS
  change S * R = 1 at hSR
  change S₁.IsHermitian at hS₁
  change R₁.IsHermitian at hR₁
  change S₁ * S₁ = A₁ at hSS₁
  change R₁ * S₁ = 1 at hRS₁
  change S₁ * R₁ = 1 at hSR₁
  change S₂.IsHermitian at hS₂
  change R₂.IsHermitian at hR₂
  change S₂ * S₂ = A₂ at hSS₂
  change R₂ * S₂ = 1 at hRS₂
  change S₂ * R₂ = 1 at hSR₂
  let B₁ := R₁ * H₁ * R₁
  let B₂ := R₂ * H₂ * R₂
  have hB₁ : B₁.PosDef := by
    have hu : IsUnit R₁ := ⟨⟨R₁, S₁, hRS₁, hSR₁⟩, rfl⟩
    simpa only [B₁, hR₁.eq] using hH₁.conjTranspose_mul_mul_same
      (B := R₁) (Matrix.mulVec_injective_of_isUnit hu)
  have hB₂ : B₂.PosDef := by
    have hu : IsUnit R₂ := ⟨⟨R₂, S₂, hRS₂, hSR₂⟩, rfl⟩
    simpa only [B₂, hR₂.eq] using hH₂.conjTranspose_mul_mul_same
      (B := R₂) (Matrix.mulVec_injective_of_isUnit hu)
  let K₁ := Real.sqrt t • (S₁ * R)
  let K₂ := Real.sqrt (1 - t) • (S₂ * R)
  have hK₁ : K₁.conjTranspose = Real.sqrt t • (R * S₁) := by
    simp [K₁, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hR.eq, hS₁.eq]
  have hK₂ : K₂.conjTranspose = Real.sqrt (1 - t) • (R * S₂) := by
    simp [K₂, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hR.eq, hS₂.eq]
  have hK : K₁.conjTranspose * K₁ + K₂.conjTranspose * K₂ = 1 := by
    rw [hK₁, hK₂]
    dsimp only [K₁, K₂]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Real.mul_self_sqrt ht₀, Real.mul_self_sqrt htbar]
    calc
      t • (R * S₁ * (S₁ * R)) + (1 - t) • (R * S₂ * (S₂ * R)) =
          R * (t • (S₁ * S₁) + (1 - t) • (S₂ * S₂)) * R := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_assoc]
      _ = R * A * R := by rw [hSS₁, hSS₂]
      _ = 1 := by rw [← hSS]; simp only [← Matrix.mul_assoc, hRS, Matrix.one_mul, hSR]
  have hn (Sj Rj Hj : Matrix (Fin d) (Fin d) ℂ)
      (hij : Sj * Rj = 1) (hji : Rj * Sj = 1) :
      R * Sj * (Rj * Hj * Rj) * (Sj * R) = R * Hj * R := by
    calc
      _ = R * (Sj * Rj) * Hj * (Rj * Sj) * R := by noncomm_ring
      _ = _ := by rw [hij, hji]; simp
  have hnorm : K₁.conjTranspose * B₁ * K₁ + K₂.conjTranspose * B₂ * K₂ =
      R * (t • H₁ + (1 - t) • H₂) * R := by
    rw [hK₁, hK₂]
    dsimp only [K₁, K₂, B₁, B₂]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Real.mul_self_sqrt ht₀, Real.mul_self_sqrt htbar, hn S₁ R₁ H₁ hSR₁ hRS₁,
      hn S₂ R₂ H₂ hSR₂ hRS₂, Matrix.mul_add, Matrix.add_mul]
  have hj := ch8_operator_jensen (Set.Ioi 0) f hf B₁ B₂ hB₁.isHermitian hB₂.isHermitian
    (fun x hx => hB₁.isStrictlyPositive.spectrum_pos hx)
    (fun x hx => hB₂.isStrictlyPositive.spectrum_pos hx) K₁ K₂ hK
  have hc := hj.mul_mul_conjTranspose_same S
  change (S * (_ - _) * S.conjTranspose).PosSemidef at hc
  rw [hS.eq, Matrix.mul_sub, Matrix.sub_mul, hnorm] at hc
  have hsand (r : ℝ) (hr : 0 ≤ r) (Sj F : Matrix (Fin d) (Fin d) ℂ) :
      S * ((Real.sqrt r • (R * Sj)) * F * (Real.sqrt r • (Sj * R))) * S =
        r • (Sj * F * Sj) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hr]
    congr 1
    calc
      _ = (S * R) * Sj * F * Sj * (R * S) := by noncomm_ring
      _ = _ := by rw [hSR, hRS]; simp
  change loewnerLE (S * ch8_matrixFunction f (R * (t • H₁ + (1 - t) • H₂) * R) * S)
    (t • (S₁ * ch8_matrixFunction f B₁ * S₁) +
      (1 - t) • (S₂ * ch8_matrixFunction f B₂ * S₂))
  simpa only [loewnerLE, Matrix.mul_add, Matrix.add_mul, hK₁, hK₂, K₁, K₂,
    hsand t ht₀ S₁ (ch8_matrixFunction f B₁),
    hsand (1 - t) htbar S₂ (ch8_matrixFunction f B₂)] using hc



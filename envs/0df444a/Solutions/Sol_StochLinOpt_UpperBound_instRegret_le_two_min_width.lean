-- Prove2me | solution 1 for StochLinOpt.UpperBound.instRegret_le_two_min_width
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:56:40.591819+00:00
-- url     : https://prove2.me/submissions/f1118737-81a6-40e0-96fb-623835e0c453

import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix

namespace StochLinOpt.UpperBound

/-- The design matrix is positive definite. -/
theorem aux_irw_posDef {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) :
    (designMatrix x t).PosDef := by
  unfold designMatrix
  refine Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_sum _ fun τ _ => ?_)
  simpa using Matrix.posSemidef_vecMulVec_self_star (x τ)

/-- Cauchy–Schwarz in the `A`-norm. -/
theorem aux_irw_cs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (v y : Fin n → ℝ) :
    (v ⬝ᵥ y) ^ 2 ≤ (v ⬝ᵥ (A *ᵥ v)) * (y ⬝ᵥ (A⁻¹ *ᵥ y)) := by
  set u := A⁻¹ *ᵥ y with hu
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hAu : A *ᵥ u = y := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  have hT : Aᵀ = A := by
    have := hA.isHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hsym : ∀ p q : Fin n → ℝ, p ⬝ᵥ (A *ᵥ q) = q ⬝ᵥ (A *ᵥ p) := by
    intro p q
    rw [Matrix.dotProduct_mulVec, ← hT, Matrix.vecMul_transpose, hT, dotProduct_comm]
  have hpsd : ∀ w : Fin n → ℝ, 0 ≤ w ⬝ᵥ (A *ᵥ w) := by
    intro w
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg w
  have hq : ∀ s : ℝ, 0 ≤ (y ⬝ᵥ u) * (s * s) + (2 * (v ⬝ᵥ y)) * s + v ⬝ᵥ (A *ᵥ v) := by
    intro s
    have h := hpsd (v + s • u)
    have e1 : (v + s • u) ⬝ᵥ (A *ᵥ (v + s • u)) =
        v ⬝ᵥ (A *ᵥ v) + s * (v ⬝ᵥ (A *ᵥ u)) + s * (u ⬝ᵥ (A *ᵥ v)) +
          s * s * (u ⬝ᵥ (A *ᵥ u)) := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [e1, hsym u v, hAu, dotProduct_comm u y] at h
    nlinarith [h]
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

/-- Bound on `|v ⬝ᵥ y|` from `vᵀ A v ≤ β`. -/
theorem aux_irw_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (v y : Fin n → ℝ)
    (β : ℝ) (hv : v ⬝ᵥ (A *ᵥ v) ≤ β) :
    |v ⬝ᵥ y| ≤ Real.sqrt β * Real.sqrt (y ⬝ᵥ (A⁻¹ *ᵥ y)) := by
  have hpsd : 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg v
  have hW : 0 ≤ y ⬝ᵥ (A⁻¹ *ᵥ y) := by
    simpa using hA.inv.posSemidef.dotProduct_mulVec_nonneg y
  have hβ : 0 ≤ β := le_trans hpsd hv
  rw [← Real.sqrt_mul hβ]
  apply Real.abs_le_sqrt
  calc (v ⬝ᵥ y) ^ 2 ≤ (v ⬝ᵥ (A *ᵥ v)) * (y ⬝ᵥ (A⁻¹ *ᵥ y)) := aux_irw_cs A hA v y
    _ ≤ β * (y ⬝ᵥ (A⁻¹ *ᵥ y)) := mul_le_mul_of_nonneg_right hv hW

end StochLinOpt.UpperBound

open Matrix
open StochLinOpt.UpperBound

theorem solution {n : ℕ} (D : Set (Fin n → ℝ)) (δ : ℝ)
    (μ xstar : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1)
    (hxstar : xstar ∈ D ∧ ∀ y ∈ D, μ ⬝ᵥ xstar ≤ μ ⬝ᵥ y)
    (hrun : IsConfidenceBall2Run D δ x ℓ) (t : ℕ) (ht : 1 ≤ t)
    (hμ : μ ∈ confBall δ x ℓ t) :
    μ ⬝ᵥ x t - μ ⬝ᵥ xstar ≤ 2 * min (Real.sqrt (beta n δ t) * width x t) 1 := by
  obtain ⟨hxt, μt, hμt, hmin⟩ := hrun t ht
  have h1 : μt ⬝ᵥ x t ≤ μ ⬝ᵥ xstar := hmin μ hμ xstar hxstar.1
  have hA := aux_irw_posDef x t
  have b1 := aux_irw_bound (designMatrix x t) hA (μ - muHat x ℓ t) (x t) (beta n δ t) hμ
  have b2 := aux_irw_bound (designMatrix x t) hA (μt - muHat x ℓ t) (x t) (beta n δ t) hμt
  have hw : Real.sqrt (x t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ x t)) = width x t := rfl
  rw [hw] at b1 b2
  rw [sub_dotProduct] at b1 b2
  have hA1 := abs_le.mp (hμD (x t) hxt)
  have hA2 := abs_le.mp (hμD xstar hxstar.1)
  have k1 := (abs_le.mp b1).2
  have k2 := (abs_le.mp b2).1
  rcases min_choice (Real.sqrt (beta n δ t) * width x t) 1 with h | h
  · rw [h]; linarith
  · rw [h]; linarith

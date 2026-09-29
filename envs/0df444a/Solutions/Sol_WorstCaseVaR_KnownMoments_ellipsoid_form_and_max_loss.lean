-- Prove2me | solution 1 for WorstCaseVaR.KnownMoments.ellipsoid_form_and_max_loss
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:38:06.151087+00:00
-- url     : https://prove2.me/submissions/f72cfb9d-5527-48ce-876e-9c5cbb0525c3

import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

theorem aux_ekm_schur {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef)
    (v : Fin n → ℝ) (c : ℝ) :
    (bordered Γ v c).PosSemidef ↔ v ⬝ᵥ Γ⁻¹ *ᵥ v ≤ c := by
  have := hΓ.isUnit.invertible
  have hB : (Matrix.of fun (_ : Fin 1) j => v j) = (Matrix.of fun i (_ : Fin 1) => v i)ᴴ := by
    ext i j; simp
  unfold bordered
  rw [hB, Matrix.PosDef.fromBlocks₁₁ _ _ hΓ]
  have hS : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => c) -
      (Matrix.of fun i (_ : Fin 1) => v i)ᴴ * Γ⁻¹ * (Matrix.of fun i (_ : Fin 1) => v i)
      = Matrix.diagonal (fun _ => c - v ⬝ᵥ Γ⁻¹ *ᵥ v) := by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hS, posSemidef_diagonal_iff]
  constructor
  · intro h; linarith [h 0]
  · intro h _; linarith

theorem aux_ekm_symm {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef)
    (x y : Fin n → ℝ) : x ⬝ᵥ Γ *ᵥ y = (Γ *ᵥ x) ⬝ᵥ y := by
  have hT : Γᵀ = Γ := by simpa using hΓ.isHermitian.eq
  rw [dotProduct_mulVec, ← mulVec_transpose, hT]

theorem aux_ekm_cs {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef) (d w : Fin n → ℝ) :
    (d ⬝ᵥ w) ^ 2 ≤ (d ⬝ᵥ Γ⁻¹ *ᵥ d) * (w ⬝ᵥ Γ *ᵥ w) := by
  have hdet : IsUnit Γ.det := (Matrix.isUnit_iff_isUnit_det Γ).mp hΓ.isUnit
  have hΓu : Γ *ᵥ (Γ⁻¹ *ᵥ d) = d := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have key : ∀ t : ℝ, 0 ≤ (w ⬝ᵥ Γ *ᵥ w) * (t * t) + (2 * (d ⬝ᵥ w)) * t
      + (d ⬝ᵥ Γ⁻¹ *ᵥ d) := by
    intro t
    have h := hΓ.posSemidef.dotProduct_mulVec_nonneg (Γ⁻¹ *ᵥ d + t • w)
    rw [star_trivial] at h
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hΓu] at h
    have h1 : w ⬝ᵥ d = d ⬝ᵥ w := dotProduct_comm _ _
    have h2 : (Γ⁻¹ *ᵥ d) ⬝ᵥ d = d ⬝ᵥ Γ⁻¹ *ᵥ d := dotProduct_comm _ _
    have h3 : (Γ⁻¹ *ᵥ d) ⬝ᵥ Γ *ᵥ w = d ⬝ᵥ w := by rw [aux_ekm_symm Γ hΓ, hΓu]
    rw [h1, h2, h3] at h
    nlinarith [h]
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith [this]

theorem aux_ekm_inner {n : ℕ} (x w : EuclideanSpace ℝ (Fin n)) : ⟪x, w⟫_ℝ = ⇑x ⬝ᵥ ⇑w := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

end WorstCaseVaR.KnownMoments

open WorstCaseVaR.KnownMoments
open MeasureTheory Matrix
open scoped InnerProductSpace

theorem solution {n : ℕ}
    (xhat w : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ x : EuclideanSpace ℝ (Fin n),
        (bordered Γ ⇑(x - xhat) (kappa ε ^ 2)).PosSemidef ↔
          ⇑(x - xhat) ⬝ᵥ Γ⁻¹ *ᵥ ⇑(x - xhat) ≤ kappa ε ^ 2) ∧
    IsGreatest {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin n),
        (bordered Γ ⇑(x - xhat) (kappa ε ^ 2)).PosSemidef ∧ r = -⟪x, w⟫_ℝ}
      (kappa ε * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ) := by
  have part1 : ∀ x : EuclideanSpace ℝ (Fin n),
      (bordered Γ ⇑(x - xhat) (kappa ε ^ 2)).PosSemidef ↔
        ⇑(x - xhat) ⬝ᵥ Γ⁻¹ *ᵥ ⇑(x - xhat) ≤ kappa ε ^ 2 :=
    fun x => aux_ekm_schur Γ hΓ _ _
  have hk : 0 ≤ kappa ε := Real.sqrt_nonneg _
  have hdet : IsUnit Γ.det := (Matrix.isUnit_iff_isUnit_det Γ).mp hΓ.isUnit
  have ha : 0 ≤ ⇑w ⬝ᵥ Γ *ᵥ ⇑w := by
    simpa using hΓ.posSemidef.dotProduct_mulVec_nonneg (⇑w)
  refine ⟨part1, ?_, ?_⟩
  · rcases ha.eq_or_lt with h0 | hpos
    · refine ⟨xhat, ?_, ?_⟩
      · rw [part1]; simp; positivity
      · rw [← h0]; simp
    · have hs : 0 < Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) := Real.sqrt_pos.mpr hpos
      have hss := Real.sq_sqrt ha
      set s := Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) with hs_def
      set a := ⇑w ⬝ᵥ Γ *ᵥ ⇑w with ha_def
      refine ⟨xhat - (kappa ε / s) • WithLp.toLp 2 (Γ *ᵥ ⇑w), ?_, ?_⟩
      · rw [part1]
        have e : ⇑(xhat - (kappa ε / s) • WithLp.toLp 2 (Γ *ᵥ ⇑w) - xhat)
            = -(kappa ε / s) • (Γ *ᵥ ⇑w) := by
          ext i; simp
        rw [e]
        have e2 : Γ⁻¹ *ᵥ (Γ *ᵥ ⇑w) = ⇑w := by
          rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
        have e3 : (Γ *ᵥ ⇑w) ⬝ᵥ ⇑w = a := by rw [ha_def, aux_ekm_symm Γ hΓ]
        simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, e2, e3, smul_eq_mul]
        have : (kappa ε / s) ^ 2 * a = kappa ε ^ 2 := by
          rw [div_pow, hss]; field_simp
        nlinarith [this]
      · rw [aux_ekm_inner, aux_ekm_inner]
        have e : ⇑(xhat - (kappa ε / s) • WithLp.toLp 2 (Γ *ᵥ ⇑w))
            = ⇑xhat - (kappa ε / s) • (Γ *ᵥ ⇑w) := by
          ext i; simp
        rw [e, sub_dotProduct, smul_dotProduct, smul_eq_mul]
        have e3 : (Γ *ᵥ ⇑w) ⬝ᵥ ⇑w = a := by rw [ha_def, aux_ekm_symm Γ hΓ]
        rw [e3]
        have : kappa ε / s * a = kappa ε * s := by
          rw [← hss]; field_simp
        linarith
  · rintro r ⟨x, hx, rfl⟩
    rw [part1] at hx
    have hcs := aux_ekm_cs Γ hΓ (⇑(x - xhat)) (⇑w)
    have hss := Real.sq_sqrt ha
    have hs0 := Real.sqrt_nonneg (⇑w ⬝ᵥ Γ *ᵥ ⇑w)
    have hb : ⇑(x - xhat) ⬝ᵥ ⇑w = ⟪x, w⟫_ℝ - ⟪xhat, w⟫_ℝ := by
      rw [aux_ekm_inner, aux_ekm_inner]
      have : ⇑(x - xhat) = ⇑x - ⇑xhat := by ext i; simp
      rw [this, sub_dotProduct]
    rw [hb] at hcs
    have h2 : (⟪x, w⟫_ℝ - ⟪xhat, w⟫_ℝ) ^ 2 ≤ (kappa ε * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w)) ^ 2 := by
      rw [mul_pow, hss]
      exact hcs.trans (mul_le_mul_of_nonneg_right hx ha)
    nlinarith [h2, mul_nonneg hk hs0]

-- Prove2me | solution 1 for RobustSDP.FullPert.well_posed
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:31:20.111528+00:00
-- url     : https://prove2.me/submissions/32a1b244-bee0-4a12-a2f1-2c7f4c1d26ae

import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator


namespace RobustSDP.FullPert

/-- The L2 operator norm is attained on a vector (or the matrix norm is zero). -/
lemma wp_attain {p q : ℕ} (D : Matrix (Fin q) (Fin p) ℝ) (hD : 0 < ‖D‖) :
    ∃ u : EuclideanSpace ℝ (Fin p), ‖u‖ = 1 ∧
      ‖(WithLp.toLp 2 (D *ᵥ WithLp.ofLp u) : EuclideanSpace ℝ (Fin q))‖ = ‖D‖ := by
  set T : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin q) :=
    (toEuclideanLin (𝕜 := ℝ) (m := Fin q) (n := Fin p)).trans LinearMap.toContinuousLinearMap D
    with hT
  have hTx : ∀ x, T x = WithLp.toLp 2 (D *ᵥ WithLp.ofLp x) := fun x => rfl
  have hDT : ‖D‖ = ‖T‖ := rfl
  by_cases hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin p)) 1).Nonempty
  · obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin p)) 1).exists_isMaxOn hne
      (continuous_norm.comp T.continuous).continuousOn
    have hu1 : ‖u‖ = 1 := by simpa using hu
    refine ⟨u, hu1, ?_⟩
    rw [← hTx]
    apply le_antisymm
    · rw [hDT]; simpa [hu1] using T.le_opNorm u
    · rw [hDT]
      refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
      by_cases hx : x = 0
      · simp [hx]
      · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin p)) 1 := by
          simp [norm_smul, hxn.ne']
        have h0 : ‖T (‖x‖⁻¹ • x)‖ ≤ ‖T u‖ := hmax hmem
        rw [map_smul, norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hxn] at h0
        have this := h0
        linarith [mul_comm ‖x‖ ‖T u‖]
  · exfalso
    have : ‖T‖ ≤ 0 := by
      refine T.opNorm_le_bound le_rfl fun x => ?_
      by_cases hx : x = 0
      · simp [hx]
      · exfalso; apply hne
        have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        exact ⟨‖x‖⁻¹ • x, by simp [norm_smul, hxn.ne']⟩
    rw [← hDT] at this; linarith

theorem well_posed_core {p q : ℕ} (D : Matrix (Fin q) (Fin p) ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ Δ : Matrix (Fin p) (Fin q) ℝ, ‖Δ‖ ≤ ρ → (1 - D * Δ).det ≠ 0) ↔ ‖D‖ < ρ⁻¹ := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hσ : 0 < ‖D‖ := lt_of_lt_of_le (inv_pos.mpr hρ) hc
    obtain ⟨u, hu1, huD⟩ := wp_attain D hσ
    set σ := ‖D‖ with hσdef
    set w : Fin q → ℝ := D *ᵥ WithLp.ofLp u with hw
    have hww : w ⬝ᵥ w = σ ^ 2 := by
      rw [← huD, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
      simp
    set Δ : Matrix (Fin p) (Fin q) ℝ := (σ ^ 2)⁻¹ • vecMulVec (WithLp.ofLp u) w with hΔ
    have hnorm : ‖Δ‖ ≤ ρ := by
      have h1 : ‖Δ‖ ≤ σ⁻¹ := by
        rw [l2_opNorm_def]
        refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hσ.le) fun x => ?_
        change ‖(WithLp.toLp 2 (Δ *ᵥ WithLp.ofLp x) : EuclideanSpace ℝ (Fin p))‖ ≤ σ⁻¹ * ‖x‖
        have he : (WithLp.toLp 2 (Δ *ᵥ WithLp.ofLp x) : EuclideanSpace ℝ (Fin p)) =
            ((σ ^ 2)⁻¹ * (w ⬝ᵥ WithLp.ofLp x)) • u := by
          rw [hΔ, smul_mulVec, vecMulVec_mulVec]
          ext i
          simp [mul_assoc, mul_comm, mul_left_comm]
        rw [he, norm_smul, hu1, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
        have hcs : |w ⬝ᵥ WithLp.ofLp x| ≤ σ * ‖x‖ := by
          have := abs_real_inner_le_norm (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin q)) x
          rw [EuclideanSpace.inner_eq_star_dotProduct] at this
          simp only [star_trivial] at this
          rw [dotProduct_comm]
          have hwn : ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin q))‖ = σ := huD
          rw [hwn] at this
          simpa using this
        calc (σ ^ 2)⁻¹ * |w ⬝ᵥ WithLp.ofLp x| ≤ (σ ^ 2)⁻¹ * (σ * ‖x‖) :=
              mul_le_mul_of_nonneg_left hcs (by positivity)
          _ = σ⁻¹ * ‖x‖ := by field_simp
      have h2 : σ⁻¹ ≤ ρ := by
        rw [inv_le_comm₀ hσ hρ]; exact hc
      linarith
    apply h Δ hnorm
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨w, ?_, ?_⟩
    · intro h0
      have : σ ^ 2 = 0 := by rw [← hww, h0]; simp
      exact hσ.ne' (by simpa using this)
    · rw [sub_mulVec, one_mulVec, hΔ, Matrix.mul_smul, mul_vecMulVec, smul_mulVec, vecMulVec_mulVec, ← hw,
        hww]
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, Pi.zero_apply]
      field_simp
      ring
  · intro hD Δ hΔ
    have h1 : ‖D * Δ‖ < 1 := by
      calc ‖D * Δ‖ ≤ ‖D‖ * ‖Δ‖ := l2_opNorm_mul D Δ
        _ ≤ ‖D‖ * ρ := mul_le_mul_of_nonneg_left hΔ (norm_nonneg _)
        _ < ρ⁻¹ * ρ := mul_lt_mul_of_pos_right hD hρ
        _ = 1 := inv_mul_cancel₀ hρ.ne'
    have hu : IsUnit (1 - D * Δ) := (Units.oneSub (D * Δ) h1).isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end RobustSDP.FullPert

open RobustSDP.FullPert


theorem solution {p q : ℕ} (D : Matrix (Fin q) (Fin p) ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ Δ : Matrix (Fin p) (Fin q) ℝ, ‖Δ‖ ≤ ρ → (1 - D * Δ).det ≠ 0) ↔ ‖D‖ < ρ⁻¹ := by
  exact well_posed_core D ρ hρ

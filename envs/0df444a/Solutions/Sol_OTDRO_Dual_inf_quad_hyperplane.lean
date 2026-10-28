-- Prove2me | solution 1 for OTDRO.Dual.inf_quad_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:51:26.510983+00:00
-- url     : https://prove2.me/submissions/e769d6db-d1f7-41f3-a1c4-81cf765f612b

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

open Matrix

open OTDRO.Dual in
theorem solution {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (β : EuclideanSpace ℝ (Fin d)) (hβ : β ≠ 0) (c : ℝ) :
    IsLeast
      {q : ℝ | ∃ Δ : EuclideanSpace ℝ (Fin d),
        inner ℝ β Δ = c ∧ q = dotProduct Δ.ofLp (Q *ᵥ Δ.ofLp)}
      (c ^ 2 / dotProduct β.ofLp (Q⁻¹ *ᵥ β.ofLp)) := by
  set b := β.ofLp with hbdef
  set w := Q⁻¹ *ᵥ b with hwdef
  set k := b ⬝ᵥ w with hkdef
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
  have hQw : Q *ᵥ w = b := by
    rw [hwdef, mulVec_mulVec, mul_nonsing_inv Q hdet, one_mulVec]
  have hb0 : b ≠ 0 := by
    intro h
    apply hβ
    have : WithLp.toLp 2 b = WithLp.toLp 2 (0 : Fin d → ℝ) := by rw [h]
    simpa [hbdef] using this
  have hk : 0 < k := by
    have := hQ.inv.dotProduct_mulVec_pos hb0
    rw [star_trivial] at this
    exact this
  have hsym : Qᵀ = Q := by
    have := hQ.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hinner : ∀ Δ : EuclideanSpace ℝ (Fin d), inner ℝ β Δ = Δ.ofLp ⬝ᵥ b := by
    intro Δ
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  have hkne : k ≠ 0 := hk.ne'
  constructor
  · refine ⟨WithLp.toLp 2 ((c / k) • w), ?_, ?_⟩
    · rw [hinner]
      simp only [WithLp.ofLp_toLp, smul_dotProduct, smul_eq_mul]
      rw [dotProduct_comm, ← hkdef]
      field_simp
    · simp only [WithLp.ofLp_toLp, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [hQw, dotProduct_comm w b, ← hkdef]
      field_simp
  · rintro q ⟨Δ, hΔ, rfl⟩
    set v := Δ.ofLp
    have hv : v ⬝ᵥ b = c := by rw [← hinner]; exact hΔ
    set t := c / k
    have e1 : v ⬝ᵥ (Q *ᵥ w) = c := by rw [hQw, hv]
    have e2 : w ⬝ᵥ (Q *ᵥ v) = c := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hsym, hQw, dotProduct_comm, hv]
    have e3 : w ⬝ᵥ (Q *ᵥ w) = k := by rw [hQw, dotProduct_comm]
    have hnn := hQ.posSemidef.dotProduct_mulVec_nonneg (v - t • w)
    rw [star_trivial] at hnn
    have hexp : (v - t • w) ⬝ᵥ (Q *ᵥ (v - t • w)) = v ⬝ᵥ (Q *ᵥ v) - t * (v ⬝ᵥ (Q *ᵥ w))
        - t * (w ⬝ᵥ (Q *ᵥ v)) + t * t * (w ⬝ᵥ (Q *ᵥ w)) := by
      simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      ring
    rw [hexp, e1, e2, e3] at hnn
    have h1 : t * c = c ^ 2 / k := by simp only [t]; field_simp
    have h2 : t * t * k = c ^ 2 / k := by simp only [t]; field_simp
    linarith

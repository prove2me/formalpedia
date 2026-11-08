-- Prove2me | solution 1 for RobustToDynamics.step2_support_function
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:01:12.310304+00:00
-- url     : https://prove2.me/submissions/c72830de-049b-467d-8b7f-0f253767e726

import Mathlib
import Definitions.Def_RobustToDynamics_ellipsoid

open Matrix

open RobustToDynamics in
theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (a : Fin n → ℝ) :
    IsGreatest ((fun x => a ⬝ᵥ x) '' ellipsoid M 1) (Real.sqrt (a ⬝ᵥ (M⁻¹ *ᵥ a))) := by
  have hT : Mᵀ = M := by
    have := hM.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hsym : ∀ u v : Fin n → ℝ, u ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (M *ᵥ u) := by
    intro u v
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]
  have hnn : ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (M *ᵥ v) := by
    intro v
    have := hM.posSemidef.dotProduct_mulVec_nonneg v
    simpa using this
  have hpos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (M *ᵥ v) := by
    intro v hv
    have := hM.dotProduct_mulVec_pos hv
    simpa using this
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  set b := M⁻¹ *ᵥ a with hb
  have hMb : M *ᵥ b = a := by
    rw [hb, mulVec_mulVec, mul_nonsing_inv M hdet, one_mulVec]
  set s := a ⬝ᵥ b with hs
  have hsb : b ⬝ᵥ (M *ᵥ b) = s := by rw [hMb, dotProduct_comm]
  have hs0 : 0 ≤ s := hsb ▸ hnn b
  rcases hs0.lt_or_eq with hs1 | hs1
  · constructor
    · refine ⟨(Real.sqrt s)⁻¹ • b, ?_, ?_⟩
      · simp only [ellipsoid, Set.mem_setOf_eq]
        rw [mulVec_smul, hMb, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          dotProduct_comm b a, ← hs]
        have h1 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0
        have h2 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs1
        have : (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * s) = 1 := by
          calc (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * s)
              = (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * (Real.sqrt s * Real.sqrt s)) := by
                rw [Real.mul_self_sqrt hs0]
            _ = 1 := by
                field_simp
        linarith
      · simp only
        rw [dotProduct_smul, smul_eq_mul, ← hs]
        have h1 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0
        have h2 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs1
        calc (Real.sqrt s)⁻¹ * s = (Real.sqrt s)⁻¹ * (Real.sqrt s * Real.sqrt s) := by
              rw [Real.mul_self_sqrt hs0]
          _ = Real.sqrt s := by rw [← mul_assoc, inv_mul_cancel₀ h2.ne', one_mul]
    · rintro _ ⟨x, hx, rfl⟩
      simp only [ellipsoid, Set.mem_setOf_eq] at hx
      set r := a ⬝ᵥ x with hr
      set c := r / s with hc
      have hq := hnn (x - c • b)
      have hbx : b ⬝ᵥ (M *ᵥ x) = r := by rw [hsym, hMb, dotProduct_comm, hr]
      rw [mulVec_sub, mulVec_smul, hMb] at hq
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul] at hq
      have hxa : x ⬝ᵥ a = r := by rw [dotProduct_comm]
      have hba : b ⬝ᵥ a = s := by rw [dotProduct_comm]
      rw [hbx, hxa, hba] at hq
      have e : x ⬝ᵥ (M *ᵥ x) - c * r - c * (r - c * s) = x ⬝ᵥ (M *ᵥ x) - r ^ 2 / s := by
        rw [hc]; field_simp; ring
      rw [e] at hq
      have h3 : r ^ 2 / s ≤ 1 := by linarith
      have h4 : r ^ 2 ≤ s := (div_le_one hs1).mp h3
      exact (le_abs_self r).trans (Real.abs_le_sqrt h4)
  · have hb0 : b = 0 := by
      by_contra h
      have := hpos b h
      rw [hsb] at this
      linarith
    have ha0 : a = 0 := by rw [← hMb, hb0, mulVec_zero]
    rw [← hs1, Real.sqrt_zero]
    constructor
    · refine ⟨0, ?_, ?_⟩
      · simp only [ellipsoid, Set.mem_setOf_eq, mulVec_zero, dotProduct_zero]
        exact zero_le_one
      · simp
    · rintro _ ⟨x, _, rfl⟩
      simp [ha0]

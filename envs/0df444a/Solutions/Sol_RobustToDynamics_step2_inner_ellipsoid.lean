-- Prove2me | solution 1 for RobustToDynamics.step2_inner_ellipsoid
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:12:01.288855+00:00
-- url     : https://prove2.me/submissions/dcafc6da-d1da-4122-9c04-6486f6b59c42

import Mathlib
import Definitions.Def_RobustToDynamics_polyhedron
import Definitions.Def_RobustToDynamics_ellipsoid
import Definitions.Def_RobustToDynamics_alpha1

set_option autoImplicit false

open Matrix RobustToDynamics

open Classical in
theorem solution {m n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (h0 : (0 : Fin n → ℝ) ∈ interior (polyhedron A b)) :
    (∀ i, A i ≠ 0 → 0 < b i) ∧ 0 < alpha1 M A b ∧
      ellipsoid M (alpha1 M A b) ⊆ polyhedron A b := by
  have hMsymm : M.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hM.1
  have hMpsd : ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (M *ᵥ v) := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp
    · exact le_of_lt (by simpa using (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hv)
  have hMinv : M⁻¹.PosDef := hM.inv
  have hMinv_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (M⁻¹ *ᵥ v) := by
    intro v hv
    simpa using (Matrix.posDef_iff_dotProduct_mulVec.mp hMinv).2 hv
  have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hM_mul_inv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMdet
  have hb_pos : ∀ i : Fin m, A i ≠ 0 → 0 < b i := by
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
    intro i hAi
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hAi
    have hAi_sq : 0 < A i ⬝ᵥ A i :=
      Finset.sum_pos' (fun k _ => mul_self_nonneg (A i k))
        ⟨j, Finset.mem_univ j, mul_self_pos.mpr hj⟩
    set δ := ε / (2 * (‖A i‖ + 1))
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hnorm_lt : ‖δ • A i‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      have h1 : δ * (2 * (‖A i‖ + 1)) = ε := div_mul_cancel₀ ε (by positivity)
      have h2 : 0 ≤ ‖A i‖ := norm_nonneg _
      nlinarith
    have hmem : δ • A i ∈ polyhedron A b :=
      hball (by simpa [Metric.mem_ball, dist_zero_right] using hnorm_lt)
    have hrow : (A *ᵥ (δ • A i)) i ≤ b i := hmem i
    have hval : (A *ᵥ (δ • A i)) i = δ * (A i ⬝ᵥ A i) := by
      simp [mulVec]
    rw [hval] at hrow
    exact lt_of_lt_of_le (mul_pos hδ hAi_sq) hrow
  have hα_pos : 0 < alpha1 M A b := by
    unfold alpha1
    split_ifs with hne
    · refine (Finset.lt_inf'_iff hne).mpr fun i hi => ?_
      have hAi : A i ≠ 0 := (Finset.mem_filter.mp hi).2
      exact div_pos (sq_pos_of_pos (hb_pos i hAi)) (hMinv_pos (A i) hAi)
    · exact zero_lt_one
  refine ⟨hb_pos, hα_pos, ?_⟩
  intro x hx i
  by_cases hAi : A i = 0
  · have h0P : (0 : Fin n → ℝ) ∈ polyhedron A b := interior_subset h0
    have hb0 : 0 ≤ b i := by simpa [polyhedron] using h0P i
    have hAx0 : (A *ᵥ x) i = 0 := by
      change A i ⬝ᵥ x = 0
      simp [hAi]
    linarith
  · have hbi : 0 < b i := hb_pos i hAi
    set η := A i ⬝ᵥ (M⁻¹ *ᵥ A i)
    have hη : 0 < η := hMinv_pos (A i) hAi
    have hα_le : alpha1 M A b ≤ b i ^ 2 / η := by
      unfold alpha1
      have himem : i ∈ Finset.univ.filter (fun k : Fin m => A k ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hAi⟩
      rw [dif_pos ⟨i, himem⟩]
      exact Finset.inf'_le _ himem
    set t := (A i ⬝ᵥ x) / η
    let w : Fin n → ℝ := x - t • (M⁻¹ *ᵥ A i)
    have hw0 : 0 ≤ w ⬝ᵥ (M *ᵥ w) := hMpsd w
    have hMMi : M *ᵥ (M⁻¹ *ᵥ A i) = A i := by
      rw [Matrix.mulVec_mulVec, hM_mul_inv, Matrix.one_mulVec]
    have hcross : (M⁻¹ *ᵥ A i) ⬝ᵥ (M *ᵥ x) = A i ⬝ᵥ x := by
      have h1 : x ⬝ᵥ (Mᵀ *ᵥ (M⁻¹ *ᵥ A i)) = (M⁻¹ *ᵥ A i) ⬝ᵥ (M *ᵥ x) := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
      rw [hMsymm.eq, hMMi, dotProduct_comm x (A i)] at h1
      exact h1.symm
    have hw_exp : w ⬝ᵥ (M *ᵥ w) =
        x ⬝ᵥ (M *ᵥ x) - 2 * t * (A i ⬝ᵥ x) + t ^ 2 * η := by
      simp only [w, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hMMi, hcross, dotProduct_comm x (A i),
        dotProduct_comm (M⁻¹ *ᵥ A i) (A i)]
      simp only [η]
      ring
    rw [hw_exp] at hw0
    have hcs : (A i ⬝ᵥ x) ^ 2 ≤ η * (x ⬝ᵥ (M *ᵥ x)) := by
      have htη : t * η = A i ⬝ᵥ x := div_mul_cancel₀ _ hη.ne'
      have hmul := mul_nonneg hη.le hw0
      have hid : η * (x ⬝ᵥ (M *ᵥ x) - 2 * t * (A i ⬝ᵥ x) + t ^ 2 * η) =
          η * (x ⬝ᵥ (M *ᵥ x)) - (A i ⬝ᵥ x) ^ 2 := by
        calc η * (x ⬝ᵥ (M *ᵥ x) - 2 * t * (A i ⬝ᵥ x) + t ^ 2 * η)
            = η * (x ⬝ᵥ (M *ᵥ x)) - 2 * (t * η) * (A i ⬝ᵥ x) + (t * η) ^ 2 := by ring
          _ = η * (x ⬝ᵥ (M *ᵥ x)) - (A i ⬝ᵥ x) ^ 2 := by rw [htη]; ring
      linarith
    have hxM : x ⬝ᵥ (M *ᵥ x) ≤ alpha1 M A b := hx
    have hα_mul : η * alpha1 M A b ≤ b i ^ 2 := by
      have := (le_div_iff₀ hη).mp hα_le
      linarith
    have hsq_le : (A i ⬝ᵥ x) ^ 2 ≤ b i ^ 2 := by
      calc (A i ⬝ᵥ x) ^ 2 ≤ η * (x ⬝ᵥ (M *ᵥ x)) := hcs
        _ ≤ η * alpha1 M A b := mul_le_mul_of_nonneg_left hxM hη.le
        _ ≤ b i ^ 2 := hα_mul
    change A i ⬝ᵥ x ≤ b i
    nlinarith

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.gibbsPolygonObstruction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:39:25.392456+00:00
-- url     : https://prove2.me/submissions/511afb42-7731-4962-809c-0e81c05b0d82

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

theorem g52c_psd_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (r s : ι) :
    ‖M r s‖ ^ 2 ≤ (M r r).re * (M s s).re := by
  have h2 := (hM.submatrix ![r, s]).det_nonneg
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  have hsr : M s r = star (M r s) := (hM.1.apply s r).symm
  have hrr : (M r r).im = 0 := by
    have := hM.1.apply r r
    have h3 := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at h3
    linarith
  have hss : (M s s).im = 0 := by
    have := hM.1.apply s s
    have h3 := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at h3
    linarith
  rw [hsr] at h2
  have h4 := (Complex.nonneg_iff.mp h2).1
  simp only [Complex.sub_re, Complex.mul_re, hrr, hss, mul_zero, sub_zero, Complex.star_def,
    Complex.conj_re, Complex.conj_im] at h4
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  nlinarith [h4]

theorem g52c_diag_sum {d : ℕ} (g : Fin d → ℝ) :
    Matrix.diagonal (fun i => (g i : ℂ)) = ∑ i, (g i : ℂ) • matrixUnit i i := by
  ext a b
  simp only [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, matrixUnit,
    Matrix.single_apply, smul_eq_mul]
  by_cases h : a = b
  · subst h; simp
  · simp only [h, if_false]
    rw [eq_comm]
    apply Finset.sum_eq_zero
    intro x _
    split_ifs with hx
    · exact absurd (hx.1.symm.trans hx.2) h
    · simp

theorem g52c_weighted_sum {d : ℕ} (g : Fin d → ℝ) (Phi : Mat d →ₗ[ℂ] Mat d)
    (hpres : Phi (Matrix.diagonal fun i => (g i : ℂ)) = Matrix.diagonal (fun i => (g i : ℂ)))
    (r s : Fin d) (hrs : r ≠ s) :
    (∑ i, (g i : ℂ) * Phi (matrixUnit i i) r s) = 0 := by
  have := congrFun (congrFun hpres r) s
  rw [g52c_diag_sum g, map_sum] at this
  simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at this
  rw [this]
  apply Finset.sum_eq_zero
  intro x _
  simp only [matrixUnit, Matrix.single_apply]
  split_ifs with hx
  · exact absurd (hx.1.symm.trans hx.2) hrs
  · simp

theorem g52c_cp_unit_psd {d : ℕ} (Phi : Mat d →ₗ[ℂ] Mat d)
    (hcp : QAlgorithms.Entanglement.IsCompletelyPositive Phi) (i : Fin d) :
    (Phi (matrixUnit i i)).PosSemidef := by
  let w : Fin 1 × Fin d → ℂ := Pi.single ((0 : Fin 1), i) 1
  have hX : (Matrix.vecMulVec w (star w)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star w
  have h := hcp 1 _ hX
  have hinner : ∀ p q : Fin 1, (Matrix.of fun a a' => Matrix.vecMulVec w (star w) (p, a) (q, a')) =
      matrixUnit i i := by
    intro p q
    have hp : p = 0 := Subsingleton.elim _ _
    have hq : q = 0 := Subsingleton.elim _ _
    subst hp hq
    ext a a'
    simp only [Matrix.of_apply, Matrix.vecMulVec_apply, w, Pi.star_apply, matrixUnit,
      Matrix.single_apply]
    by_cases ha : a = i
    · subst ha
      by_cases ha' : a' = a
      · subst ha'; simp [Pi.single_apply]
      · simp [Pi.single_apply, ha', Ne.symm ha']
    · simp [Pi.single_apply, ha, Ne.symm ha]
  have := h.submatrix (fun a : Fin d => ((0 : Fin 1), a))
  convert this using 1
  ext a b
  simp only [Matrix.submatrix_apply, idTensorSuperop, Matrix.of_apply]
  rw [hinner]

theorem g52c_polygon_w {d : ℕ} (z : Fin d → ℂ) (hz : ∑ i, z i = 0) (s : Fin d → ℝ) (i0 : Fin d)
    (hstrict : (∑ i ∈ Finset.univ.erase i0, s i) < s i0) (hn : ∀ i, ‖z i‖ = s i) : False := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)] at hz
  have heq : z i0 = -∑ i ∈ Finset.univ.erase i0, z i := by linear_combination hz
  have : s i0 ≤ ∑ i ∈ Finset.univ.erase i0, s i := by
    rw [← hn i0, heq, norm_neg]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun i _ => hn i)))
  linarith

end

end QAlgorithms.Papers.Independent.Information100.P44

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution {d : ℕ} (hd : 0 < d) (gamma : Fin d → ℝ)
    (hgamma : ∀ i, 0 < gamma i) (hsum : ∑ i, gamma i = 1)
    (Phi : Mat d →ₗ[ℂ] Mat d) (hcp : QAlgorithms.Entanglement.IsCompletelyPositive Phi)
    (hpres : Phi (Matrix.diagonal fun i => (gamma i : ℂ)) =
      Matrix.diagonal (fun i => (gamma i : ℂ))) (r s : Fin d) (hrs : r ≠ s) :
    (∀ i, ‖(gamma i : ℂ) * Phi (matrixUnit i i) r s‖ ≤
      gamma i * Real.sqrt (population Phi r i * population Phi s i)) ∧
    (∑ i, (gamma i : ℂ) * Phi (matrixUnit i i) r s) = 0 ∧
    (∀ i0, (∑ i ∈ Finset.univ.erase i0,
        gamma i * Real.sqrt (population Phi r i * population Phi s i)) <
      gamma i0 * Real.sqrt (population Phi r i0 * population Phi s i0) →
      ¬ ∃ Psi : Mat d →ₗ[ℂ] Mat d, QAlgorithms.Entanglement.IsCompletelyPositive Psi ∧
        Psi (Matrix.diagonal fun i => (gamma i : ℂ)) =
          Matrix.diagonal (fun i => (gamma i : ℂ)) ∧
        (∀ t i, population Psi t i = population Phi t i) ∧
        ∀ i, ‖Psi (matrixUnit i i) r s‖ =
          Real.sqrt (population Phi r i * population Phi s i)) := by
  refine ⟨?_, g52c_weighted_sum gamma Phi hpres r s hrs, ?_⟩
  · intro i
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hgamma i)]
    apply mul_le_mul_of_nonneg_left _ (hgamma i).le
    have h := g52c_psd_entry _ (g52c_cp_unit_psd Phi hcp i) r s
    apply Real.le_sqrt_of_sq_le
    simpa [population] using h
  · rintro i0 hstrict ⟨Psi, hcpP, hpresP, -, hn⟩
    refine g52c_polygon_w (fun i => (gamma i : ℂ) * Psi (matrixUnit i i) r s)
      (g52c_weighted_sum gamma Psi hpresP r s hrs) _ i0 hstrict ?_
    intro i
    show ‖(gamma i : ℂ) * Psi (matrixUnit i i) r s‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hgamma i), hn i]

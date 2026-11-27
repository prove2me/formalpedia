-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.Glob.VacU.unitary_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:29.345795+00:00
-- url     : https://prove2.me/submissions/7c330ca9-2584-4228-9bdf-5ff96aa5791e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_ExistsCircleDetNe
import Theorems.Thm_PositivityTheory_Rg_Sw_Glob_VacU_exists_circle_det_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Complex
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacU
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.Glob.VacU
theorem _root_.solution (W : Matrix (Fin n) (Fin n) ℂ) (hW : Wᴴ * W = 1) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ), Pᴴ * P = 1 ∧ P * Pᴴ = 1 ∧ (∀ j, ‖w j‖ = 1) ∧
      W = P * diagonal w * Pᴴ := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.1 hW
  obtain ⟨lam, hlam1, hdet⟩ := exists_circle_det_ne W
  have hlam0 : lam ≠ 0 := by intro h; rw [h, norm_zero] at hlam1; exact zero_ne_one hlam1
  have hconj : starRingEnd ℂ lam * lam = 1 := by
    rw [Complex.conj_mul', hlam1]; simp
  set V' := lam⁻¹ • W with hV'
  have hV'u : V'ᴴ * V' = 1 := by
    rw [hV', Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hW]
    rw [RCLike.star_def, map_inv₀]
    rw [show (starRingEnd ℂ lam)⁻¹ * lam⁻¹ = (starRingEnd ℂ lam * lam)⁻¹ by rw [mul_inv], hconj, inv_one, one_smul]
  set B := 1 + V' with hB
  set A := 1 - V' with hA
  have hBdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    have : B = lam⁻¹ • (W + lam • 1) := by
      rw [hB, hV', smul_add, smul_smul, inv_mul_cancel₀ hlam0, one_smul, add_comm]
    rw [this, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hlam0)) hdet
  set H := (Complex.I • A) * B⁻¹ with hH
  have hHB : H * B = Complex.I • A := by
    rw [hH, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBdet, Matrix.mul_one]
  have hBc : IsUnit Bᴴ.det := by rw [Matrix.det_conjTranspose]; exact hBdet.star
  have hid : Bᴴ * A = -(Aᴴ * B) := by
    rw [hB, hA, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hV'u]
    abel
  have hHerm : H.IsHermitian := by
    have hk : Bᴴ * Hᴴ * B = Bᴴ * H * B := by
      have e1 : Bᴴ * Hᴴ = -(Complex.I • Aᴴ) := by
        rw [← Matrix.conjTranspose_mul, hHB, Matrix.conjTranspose_smul]
        simp [RCLike.star_def, Complex.conj_I]
      rw [e1, Matrix.mul_assoc, hHB, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, hid, smul_neg]
    have hk2 : Hᴴ = H := by
      have := congrArg (fun M => (Bᴴ)⁻¹ * M * B⁻¹) hk
      rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBc, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hBdet, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hBc, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBdet,
        Matrix.mul_one] at this
    exact hk2
  set U : Matrix (Fin n) (Fin n) ℂ := (hHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set d : Fin n → ℝ := hHerm.eigenvalues with hd
  have hUu : Uᴴ * U = 1 := by
    rw [hU]; exact Matrix.mem_unitaryGroup_iff'.1 hHerm.eigenvectorUnitary.2
  have hUu' : U * Uᴴ = 1 := mul_eq_one_comm.1 hUu
  have hspec : H = U * diagonal (fun j => ((d j : ℝ) : ℂ)) * Uᴴ := by
    have := hHerm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hdI : ∀ j, ((d j : ℝ) : ℂ) + Complex.I ≠ 0 := by
    intro j h; have := congrArg Complex.im h; simp at this
  set E : Fin n → ℂ := fun j => (Complex.I - (d j : ℂ)) / (Complex.I + (d j : ℂ)) with hE
  have hHdiag : H + Complex.I • 1 = U * diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * Uᴴ := by
    have e : diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) = diagonal (fun j => ((d j : ℝ) : ℂ)) + Complex.I • 1 := by
      rw [Matrix.smul_one_eq_diagonal, diagonal_add]
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUu', hspec]
  have hHI : IsUnit (H + Complex.I • 1).det := by
    rw [isUnit_iff_ne_zero, hHdiag, Matrix.det_mul, Matrix.det_mul, det_diagonal]
    have hU1 : U.det * Uᴴ.det = 1 := by rw [← Matrix.det_mul, hUu', Matrix.det_one]
    intro h0
    have : U.det * Uᴴ.det * ∏ j, (((d j : ℝ) : ℂ) + Complex.I) = 0 := by
      rw [show U.det * Uᴴ.det * ∏ j, (((d j : ℝ) : ℂ) + Complex.I) = U.det * (∏ j, (((d j : ℝ) : ℂ) + Complex.I)) * Uᴴ.det by ring]
      exact h0
    rw [hU1, one_mul] at this
    exact (Finset.prod_ne_zero_iff.2 fun j _ => hdI j) this
  have hEq1 : (H + Complex.I • 1) * V' = Complex.I • 1 - H := by
    have := hHB
    rw [hB, hA, Matrix.mul_add, Matrix.mul_one, smul_sub] at this
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at this
    rw [← this]
    abel
  have hEq2 : (H + Complex.I • 1) * (U * diagonal E * Uᴴ) = Complex.I • 1 - H := by
    rw [hHdiag]
    have e1 : U * diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * Uᴴ * (U * diagonal E * Uᴴ) =
        U * (diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * diagonal E) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hUu, Matrix.one_mul]
    rw [e1, diagonal_mul_diagonal]
    have e2 : (fun j => (((d j : ℝ) : ℂ) + Complex.I) * E j) = fun j => Complex.I - ((d j : ℝ) : ℂ) := by
      funext j
      have hdI' : Complex.I + ((d j : ℝ) : ℂ) ≠ 0 := by rw [add_comm]; exact hdI j
      rw [hE]; simp only; rw [add_comm ((d j : ℝ) : ℂ) Complex.I]; field_simp
    rw [e2, hspec]
    have e3 : diagonal (fun j => Complex.I - ((d j : ℝ) : ℂ)) = Complex.I • 1 - diagonal (fun j => ((d j : ℝ) : ℂ)) := by
      rw [Matrix.smul_one_eq_diagonal, ← diagonal_sub]
    rw [e3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUu']
  have hV'eq : V' = U * diagonal E * Uᴴ := by
    have h0 : (H + Complex.I • 1) * (V' - U * diagonal E * Uᴴ) = 0 := by
      rw [Matrix.mul_sub, hEq1, hEq2, sub_self]
    have := congrArg (fun M => (H + Complex.I • 1)⁻¹ * M) h0
    simp only [Matrix.mul_zero] at this
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHI, Matrix.one_mul, sub_eq_zero] at this
    exact this
  refine ⟨U, fun j => lam * E j, hUu, hUu', ?_, ?_⟩
  · intro j
    rw [norm_mul, hlam1, one_mul, hE]
    simp only
    rw [norm_div]
    have h1 : ‖Complex.I - ((d j : ℝ) : ℂ)‖ = ‖Complex.I + ((d j : ℝ) : ℂ)‖ := by
      rw [← Complex.norm_conj (Complex.I + _)]; simp [Complex.conj_I, Complex.conj_ofReal, ← neg_add']
      rw [← norm_neg]; congr 1; ring
    rw [h1, div_self]
    intro h0; rw [norm_eq_zero] at h0; exact hdI j (by rw [add_comm]; exact h0)
  · have : W = lam • V' := by rw [hV', smul_smul, mul_inv_cancel₀ hlam0, one_smul]
    have hd2 : diagonal (fun j => lam * E j) = lam • diagonal E := by
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
    rw [this, hV'eq, hd2, Matrix.mul_smul, Matrix.smul_mul]
end PositivityTheory.Rg.Sw.Glob.VacU

-- Prove2me | solution 1 for PI.WSF.cz_svd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:15.196285+00:00
-- url     : https://prove2.me/submissions/a1c1ed0c-3b7c-4091-bae4-1ae6ed64d30b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CzDiagUnitary
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WSF
open MvPolynomial Matrix
open scoped ComplexOrder
namespace PI.WSF
theorem _root_.solution {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (hg : IsUnit g.det) :
    ∃ u ∈ unitaryGroup (Fin N) ℂ, ∃ v ∈ unitaryGroup (Fin N) ℂ, ∃ z : Fin N → ℂ,
      g = u * diagonal z * v := by
  classical
  have hA : (gᴴ * g).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self g
  have hnn : ∀ i, 0 ≤ hA.eigenvalues i := Matrix.eigenvalues_conjTranspose_mul_self_nonneg g
  set W : Matrix (Fin N) (Fin N) ℂ := (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hW
  have hWu : W ∈ unitaryGroup (Fin N) ℂ := hA.eigenvectorUnitary.2
  have hWW : Wᴴ * W = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hWu
  have hWW' : W * Wᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hWu
  have hD : Wᴴ * (gᴴ * g) * W = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    have h1 := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h1
    rw [← Matrix.star_eq_conjTranspose]
    exact h1
  have hdet : (diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix (Fin N) (Fin N) ℂ).det ≠ 0 := by
    have h1 : Wᴴ.det * W.det = 1 := by rw [← Matrix.det_mul, hWW, Matrix.det_one]
    have h2 : gᴴ.det ≠ 0 := by
      rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr hg.ne_zero
    rw [← hD, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul_eq_one h1)
      (mul_ne_zero h2 hg.ne_zero)) (right_ne_zero_of_mul_eq_one h1)
  have hpos : ∀ i, 0 < hA.eigenvalues i := by
    intro i
    rw [Matrix.det_diagonal] at hdet
    have h1 := Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)
    have h2 : hA.eigenvalues i ≠ 0 := by
      intro h3
      apply h1
      simp [h3]
    exact lt_of_le_of_ne (hnn i) (Ne.symm h2)
  set s : Fin N → ℂ := fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ) with hs
  have hs0 : ∀ i, s i ≠ 0 := by
    intro i
    simp only [hs, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr (hpos i)).ne'
  have hs2 : ∀ i, star (s i) * s i = RCLike.ofReal (hA.eigenvalues i) := by
    intro i
    change star (s i) * s i = ((hA.eigenvalues i : ℝ) : ℂ)
    simp only [hs, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hnn i)]
  refine ⟨g * W * diagonal (fun i => (s i)⁻¹), ?_, Wᴴ, ?_, s, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
    have key : diagonal (star fun i => (s i)⁻¹) * (Wᴴ * gᴴ) * (g * W * diagonal fun i => (s i)⁻¹)
        = diagonal (star fun i => (s i)⁻¹) * (Wᴴ * (gᴴ * g) * W) * diagonal fun i => (s i)⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [key, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have h1 := hs2 i
    have h2 : star (s i) ≠ 0 := star_ne_zero.mpr (hs0 i)
    simp only [Pi.star_apply, Function.comp_apply, star_inv₀, ← h1]
    field_simp
    exact div_self (hs0 i)
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact hWW
  · rw [Matrix.mul_assoc (g * W), Matrix.diagonal_mul_diagonal]
    have h1 : (fun i => (s i)⁻¹ * s i) = fun _ => (1 : ℂ) := by
      funext i; exact inv_mul_cancel₀ (hs0 i)
    rw [h1, Matrix.diagonal_one, Matrix.mul_one, Matrix.mul_assoc, hWW', Matrix.mul_one]
end PI.WSF

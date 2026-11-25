-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HadamardPSDAux_le_of_diag_pos_7e09ecc94e55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:25:00.705859+00:00
-- url     : https://prove2.me/submissions/8bb42c40-19df-4ca6-bcbc-6020978c5007

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHadamardPSD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Finset
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.HadamardPSDAux
namespace GroundTheory.Heights₂.Heights.HadamardPSDAux
theorem _root_.solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hpos : ∀ i, 0 < (A i i).re) : ‖A.det‖ ≤ ∏ i, ‖A i i‖ := by
  set d : Fin n → ℝ := fun i => (A i i).re with hd_def
  have hAd : ∀ i, A i i = (d i : ℂ) := by
    intro i
    obtain ⟨-, him⟩ := Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))
    exact Complex.ext (by simp [d]) (by simp [← him])
  set c : Fin n → ℝ := fun i => (Real.sqrt (d i))⁻¹ with hc_def
  have hc : ∀ i, 0 < c i := fun i => inv_pos.mpr (Real.sqrt_pos.mpr (hpos i))
  have hcd : ∀ i, c i * c i * d i = 1 := by
    intro i
    simp only [c]
    rw [← mul_inv, Real.mul_self_sqrt (hpos i).le, inv_mul_cancel₀ (hpos i).ne']
  obtain ⟨D, hD_def⟩ : ∃ D : Matrix (Fin n) (Fin n) ℂ, D = diagonal fun i => (c i : ℂ) := ⟨_, rfl⟩
  have hD : Dᴴ = D := by simp [hD_def, diagonal_conjTranspose]
  have hB : (D * A * D).PosSemidef := by simpa [hD] using hA.conjTranspose_mul_mul_same D
  have hBdiag : ∀ i, (D * A * D) i i = 1 := by
    intro i
    simp only [hD_def, diagonal_mul, mul_diagonal, hAd]
    exact_mod_cast (by linarith [hcd i] : c i * d i * c i = 1)
  have htr : ∑ i, hB.1.eigenvalues i = n := by
    have h := hB.1.trace_eq_sum_eigenvalues
    simp only [Matrix.trace, Matrix.diag_apply, hBdiag] at h
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    simpa using (congrArg Complex.re h).symm
  have hprod : ∏ i, hB.1.eigenvalues i ≤ 1 := by
    calc ∏ i, hB.1.eigenvalues i ≤ ∏ i, Real.exp (hB.1.eigenvalues i - 1) :=
          prod_le_prod (fun i _ => hB.eigenvalues_nonneg i)
            (fun i _ => by linarith [Real.add_one_le_exp (hB.1.eigenvalues i - 1)])
      _ = Real.exp (∑ i, (hB.1.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
      _ = 1 := by simp [sum_sub_distrib, htr]
  have hnormB : ‖(D * A * D).det‖ ≤ 1 := by
    have h1 : (D * A * D).det = ((∏ i, hB.1.eigenvalues i : ℝ) : ℂ) := by
      rw [hB.1.det_eq_prod_eigenvalues]; push_cast; rfl
    rw [h1, Complex.norm_of_nonneg (prod_nonneg fun i _ => hB.eigenvalues_nonneg i)]
    exact hprod
  have hdetB : (D * A * D).det = (((∏ i, c i) ^ 2 : ℝ) : ℂ) * A.det := by
    simp only [det_mul, hD_def, det_diagonal]
    push_cast
    ring
  have key : ‖(D * A * D).det‖ * ∏ i, d i = ‖A.det‖ := by
    rw [hdetB, norm_mul, Complex.norm_of_nonneg (by positivity)]
    calc (∏ i, c i) ^ 2 * ‖A.det‖ * ∏ i, d i = ‖A.det‖ * ∏ i, (c i * c i * d i) := by
          rw [prod_mul_distrib, prod_mul_distrib]; ring
      _ = ‖A.det‖ := by simp [hcd]
  have hnd : ∀ i, ‖A i i‖ = d i := fun i => by rw [hAd i, Complex.norm_of_nonneg (hpos i).le]
  rw [← key, prod_congr rfl fun i _ => hnd i]
  calc ‖(D * A * D).det‖ * ∏ i, d i ≤ 1 * ∏ i, d i :=
        mul_le_mul_of_nonneg_right hnormB (prod_nonneg fun i _ => (hpos i).le)
    _ = ∏ i, d i := one_mul _
end GroundTheory.Heights₂.Heights.HadamardPSDAux

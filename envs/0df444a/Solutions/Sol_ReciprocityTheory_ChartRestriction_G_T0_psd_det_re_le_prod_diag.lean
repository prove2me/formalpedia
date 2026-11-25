-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.psd_det_re_le_prod_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:34.280832+00:00
-- url     : https://prove2.me/submissions/3076cad5-ad59-454f-a34c-55fdc4258b7d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hadamard
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_psd_det_re_le_one_of_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open scoped BigOperators ComplexOrder
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosSemidef) :
    G.det.re ≤ ∏ c, (G c c).re := by
  classical
  have hdiag : ∀ c, G c c = ((G c c).re : ℂ) := fun c =>
    (Complex.conj_eq_iff_re.mp (by
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hG.1 c) c)).symm
  have hnn : ∀ c, 0 ≤ (G c c).re := fun c => (Complex.nonneg_iff.mp (hG.diag_nonneg (i := c))).1
  by_cases hz : ∃ c, (G c c).re = 0
  · obtain ⟨c, hc⟩ := hz
    have hcol : G *ᵥ Pi.single c 1 = 0 := by
      rw [← hG.dotProduct_mulVec_zero_iff]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hdiag c, hc]
      simp
    have hdet : G.det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero c
      intro i
      have h := congrFun hcol i
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
    rw [hdet, Complex.zero_re]
    exact Finset.prod_nonneg fun c _ => hnn c
  · push_neg at hz
    have hpos : ∀ c, 0 < (G c c).re := fun c => lt_of_le_of_ne (hnn c) (Ne.symm (hz c))
    set d : Fin N → ℝ := fun c => (Real.sqrt (G c c).re)⁻¹ with hd_def
    have hdr : ∀ c, d c * (G c c).re * d c = 1 := fun c => by
      have hs := Real.mul_self_sqrt (hnn c)
      have hsq : Real.sqrt (G c c).re ≠ 0 := (Real.sqrt_pos.mpr (hpos c)).ne'
      simp only [hd_def]
      field_simp
      nlinarith [hs]
    set D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal fun c => (d c : ℂ) with hD_def
    have hD : Dᴴ = D := by simp [hD_def, Matrix.diagonal_conjTranspose]
    have hH : (D * G * D).PosSemidef := by
      have h := hG.conjTranspose_mul_mul_same D
      rwa [hD] at h
    have hHd : ∀ c, (D * G * D) c c = 1 := by
      intro c
      simp only [hD_def, Matrix.diagonal_mul, Matrix.mul_diagonal]
      rw [hdiag c]
      exact_mod_cast hdr c
    have h1 := psd_det_re_le_one_of_diag N _ hH hHd
    have hdet : (D * G * D).det = (((∏ c, d c) ^ 2 : ℝ) : ℂ) * G.det := by
      simp only [hD_def, Matrix.det_mul, Matrix.det_diagonal]
      push_cast
      ring
    rw [hdet, Complex.re_ofReal_mul] at h1
    have hprod : (∏ c, d c) ^ 2 * ∏ c, (G c c).re = 1 := by
      rw [show (∏ c, d c) ^ 2 * ∏ c, (G c c).re = ∏ c, (d c * (G c c).re * d c) by
        rw [sq, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun c _ => by ring]
      exact Finset.prod_eq_one fun c _ => hdr c
    have hp : 0 < (∏ c, d c) ^ 2 :=
      pow_pos (Finset.prod_pos fun c _ => inv_pos.mpr (Real.sqrt_pos.mpr (hpos c))) 2
    by_contra hlt
    push_neg at hlt
    have := mul_lt_mul_of_pos_left hlt hp
    linarith
end ReciprocityTheory.ChartRestriction.G.T0

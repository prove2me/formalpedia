-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.gramSt_det_re_le_of_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:33.132865+00:00
-- url     : https://prove2.me/submissions/ef327b68-a1ea-4c54-8f0d-a02b1ca3c543

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_gramSt_det_one_add_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix
open scoped ComplexOrder MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {G H : Matrix ι ι ℂ} (hG : G.PosDef)
    (hGH : (H - G).PosSemidef) : G.det.re ≤ H.det.re := by
  set S := CFC.sqrt G with hSdef
  have hS0 : S.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hSh : Sᴴ = S := hS0.1
  have hdetG : G.det = S.det * S.det := by rw [← hSS, det_mul]
  have hGpos := hG.det_pos
  have hSdet : S.det ≠ 0 := by
    intro h; rw [hdetG, h, zero_mul] at hGpos; exact lt_irrefl _ hGpos
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  have hQ : (S⁻¹ * (H - G) * (S⁻¹)ᴴ).PosSemidef := hGH.mul_mul_conjTranspose_same _
  have hinvh : (S⁻¹)ᴴ = S⁻¹ := by rw [conjTranspose_nonsing_inv, hSh]
  have h2 : S * (S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S = H - G := by
    rw [hinvh, show S * (S⁻¹ * (H - G) * S⁻¹) * S = (S * S⁻¹) * (H - G) * (S⁻¹ * S) by
      simp only [Matrix.mul_assoc]]
    rw [mul_nonsing_inv S hSu, nonsing_inv_mul S hSu, Matrix.one_mul, Matrix.mul_one]
  have hH : H = S * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS, h2]; abel
  have hdetH : H.det = G.det * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ).det := by
    conv_lhs => rw [hH]
    rw [det_mul, det_mul, hdetG]; ring
  rw [hdetH, gramSt_det_one_add_eq hQ]
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hGpos
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have h1 : (1:ℝ) ≤ ∏ i, (1 + hQ.1.eigenvalues i) := by
    calc (1:ℝ) = ∏ _i : ι, (1:ℝ) := by simp
      _ ≤ ∏ i, (1 + hQ.1.eigenvalues i) :=
        Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun i _ => by linarith [hQ.eigenvalues_nonneg i])
  nlinarith
end ReciprocityTheory.GeometryOfNumbersTheory

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaPositiveGaussScalar_eq_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:19:26.639413+00:00
-- url     : https://prove2.me/submissions/60fd9707-74fb-4632-ac41-61558406b0c7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussScalar
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussFourthReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_square_scale
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0 < q)
    (γ : SL(2,ℤ)) (hc : 0 < γ 1 0) (hlevel : 16*q^2 ∣ (γ 1 0).toNat) :
    lpsThetaPositiveGaussScalar q γ =
      -(4*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsUnaryQuadraticGauss (γ 0 0) (γ 1 0).toNat^4 := by
  let c := (γ 1 0).toNat
  have hcp : 0 < c := by omega
  let : NeZero c := ⟨ne_of_gt hcp⟩
  have hci : (c:ℤ)=γ 1 0 := Int.toNat_of_nonneg hc.le
  have hdet : γ 0 0*γ 1 1-γ 0 1*(c:ℤ)=1 := by
    rw [hci]
    simpa only [Matrix.det_fin_two] using γ.det_coe
  obtain ⟨k,hk⟩ := hlevel
  have hkp : 0 < k := by
    by_contra h
    have hkz : k=0 := by omega
    simp [hkz] at hk
    omega
  have hs := lpsUnaryQuadraticGauss_square_scale c (2*q) k
    (by dsimp [c];rw [hk];ring) (by positivity) hkp (γ 0 0) (γ 0 1) (γ 1 1) hdet
  have ha : γ 0 0*((2*q:ℕ):ℤ)^2=4*(q:ℤ)^2*γ 0 0 := by push_cast;ring
  rw [ha] at hs
  unfold lpsThetaPositiveGaussScalar
  change -(32*(q:ℂ)^3*(c:ℂ)^2)⁻¹ *
    lpsUnaryQuadraticGauss (γ 0 0) c * lpsUnaryQuadraticGauss (4*(q:ℤ)^2*γ 0 0) c^3 =
      -(4*(c:ℂ)^2)⁻¹ * lpsUnaryQuadraticGauss (γ 0 0) c^4
  rw [hs]
  push_cast
  have hqC : (q:ℂ)≠0 := by exact_mod_cast ne_of_gt hq
  have hcC : (c:ℂ)≠0 := by exact_mod_cast ne_of_gt hcp
  field_simp [hqC,hcC]
  ring
end QEC.Coding.TannerLiftedProduct

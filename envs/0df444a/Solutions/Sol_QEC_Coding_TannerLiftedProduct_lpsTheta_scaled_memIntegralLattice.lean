-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsTheta_scaled_memIntegralLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:04:32.8703+00:00
-- url     : https://prove2.me/submissions/c14d31f2-fc49-4377-896d-aa3a5b4101ee

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCorrection_scaled_integer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsThetaCuspidalRemainder


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    lpsThetaIntegerDenominator q • lpsThetaCuspidalRemainder q hq4 ∈
      lpsIntegralCuspLattice ((4*q)^2) := by
  intro n
  rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
  change ∃ z : ℤ, (lpsThetaIntegerDenominator q : ℂ)*
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder q hq4)) = (z : ℂ)
  rw [coeff_qExpansion_lpsThetaCuspidalRemainder, mul_sub]
  obtain ⟨z, hz⟩ := lpsThetaCorrection_scaled_integer q n
  refine ⟨lpsThetaIntegerDenominator q*((PowerSeries.coeff n (lpsTraceThetaSeries q) : ℕ) : ℤ)-z, ?_⟩
  rw [hz, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
end QEC.Coding.TannerLiftedProduct

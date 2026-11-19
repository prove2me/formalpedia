-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsSL2Z_firstColumn_unit_modulus
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:42:31.821189+00:00
-- url     : https://prove2.me/submissions/ce7bd9a3-c250-47ec-9034-69ad363f824c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardThetaModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsStandardThetaModularForm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (γ : SL(2,ℤ))
    (hC : γ 1 0=(N:ℤ)) : IsUnit ((γ 0 0:ℤ):ZMod N) := by
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.property
  have hcast := congrArg (fun x : ℤ => (x:ZMod N)) hd
  have hN : (N:ZMod N)=0 := ZMod.natCast_self N
  rw [hC] at hcast
  push_cast at hcast
  simp only [hN,mul_zero,sub_zero] at hcast
  exact ⟨⟨_,_,hcast,by rw [mul_comm];exact hcast⟩,rfl⟩
end QEC.Coding.TannerLiftedProduct

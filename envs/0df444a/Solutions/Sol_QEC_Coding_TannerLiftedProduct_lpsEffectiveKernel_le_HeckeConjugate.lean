-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveKernel_le_HeckeConjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:54:41.715366+00:00
-- url     : https://prove2.me/submissions/3a1d539b-cc55-47b5-900e-108401d2e149

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) :
    (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.ker ≤
      lpsHeckeConjugateIntersection N p := by
  intro γ hγ
  have hh : (MulAction.toPermHom SL(2,ℤ) ℍ) γ=1 :=
    congrArg (fun e : lpsEffectiveModularGroup => (e:Equiv.Perm ℍ)) hγ
  rcases (lpsEffectiveKernel γ).mp hh with rfl | rfl
  · exact ⟨by simp,by simp [lpsUpperCongruence]⟩
  · exact ⟨by simp,by simp [lpsUpperCongruence]⟩
end QEC.Coding.TannerLiftedProduct

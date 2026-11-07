-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedTaylor_zero_of_nome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:43:58.733139+00:00
-- url     : https://prove2.me/submissions/854fce33-8654-4bcf-b3ed-ccee221517a3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedTaylor_function
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedNomeEval_function
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspNome_zero_germ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_zero_iff_germ


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (A : lpsOriginalAnalyticCuspLaurentRing)
    (hA : ∀ τ : ℍ,lpsOriginalAnalyticCuspLocalizedNomeEval τ A=0) :
    lpsOriginalAnalyticCuspLocalizedTaylor A=0 := by
  obtain ⟨n,F,hF⟩:=IsLocalization.Away.surj lpsOriginalAnalyticCuspLaurentParameter A
  have hNome (τ : ℍ) : F.val (Function.Periodic.qParam 1 (τ:ℂ))=0 := by
    have h:=congrArg (lpsOriginalAnalyticCuspLocalizedNomeEval τ) hF
    rw [map_mul,map_pow,hA τ,zero_mul,
      lpsOriginalAnalyticCuspLocalizedNomeEval_function] at h
    exact h.symm
  have hTaylor : lpsOriginalCuspTaylorRingHom F=0 :=
    (lpsOriginalTaylorSeries_zero_iff_germ F.property).mpr
      (lpsOriginalAnalyticCuspNome_zero_germ F hNome)
  have h:=congrArg lpsOriginalAnalyticCuspLocalizedTaylor hF
  rw [map_mul,map_pow,lpsOriginalAnalyticCuspLocalizedTaylor_function,
    lpsOriginalAnalyticCuspLaurentParameter_taylor,
    lpsOriginalAnalyticCuspLocalizedTaylor_function,hTaylor,map_zero] at h
  exact (IsLocalization.Away.algebraMap_isUnit
    (S:=lpsOriginalComplexCuspLaurentRing) (PowerSeries.X : PowerSeries ℂ)).pow n
      |>.mul_right_cancel (h.trans (zero_mul _).symm)
end QEC.Coding.TannerLiftedProduct

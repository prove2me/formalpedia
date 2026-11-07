-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_cyclotomicFormalProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:36:15.258475+00:00
-- url     : https://prove2.me/submissions/633cb115-6ced-42ad-87a2-e425c42c47a2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_actualTaylorProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicPrimeCoefficientEval_complex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicFormalPrimeProduct_complex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicComplexEmbedding_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (lpsOriginalCyclotomicPrimeCoefficientEval p)=
      lpsOriginalCyclotomicFormalPrimeProduct p := by
  apply Polynomial.map_injective
    (lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicComplexEmbedding p))
    (lpsOriginalCuspCoefficientMap_injective (lpsOriginalCyclotomicComplexEmbedding p)
      (lpsOriginalCyclotomicComplexEmbedding_injective p))
  rw [Polynomial.map_map,lpsOriginalCyclotomicPrimeCoefficientEval_complex,
    lpsOriginalCyclotomicFormalPrimeProduct_complex,←Polynomial.map_map]
  exact lpsOriginalPrimeIntegerPolynomial_actualTaylorProduct p
end QEC.Coding.TannerLiftedProduct

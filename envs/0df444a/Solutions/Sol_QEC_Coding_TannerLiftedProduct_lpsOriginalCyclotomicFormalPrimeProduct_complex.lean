-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicFormalPrimeProduct_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:45:39.236474+00:00
-- url     : https://prove2.me/submissions/f6bb0623-4f42-433f-ab0a-58b2a8435011

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicFiniteCuspBranch_complex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspAffineBranch_taylor_zero_phase
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_jWidth


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    (lpsOriginalCyclotomicFormalPrimeProduct p).map
      (lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicComplexEmbedding p))=
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C
        (lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticPrimeBranch p i))) := by
  classical
  rw [lpsOriginalCyclotomicFormalPrimeProduct,Polynomial.map_mul,Fintype.prod_option]
  congr 1
  · rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
      lpsOriginalCuspCoefficientMap_jWidth,lpsOriginalAnalyticPrimeBranch,
      lpsOriginalAnalyticCuspAffineBranch_taylor_zero_phase]
  · rw [Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro m _
    rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
      lpsOriginalCyclotomicFiniteCuspBranch_complex,lpsOriginalAnalyticPrimeBranch]
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCosetBranch_nome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:37:07.594438+00:00
-- url     : https://prove2.me/submissions/0a521a12-49cf-4a83-a8a3-444c3fc0d341

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspAffineBranch_nome


set_option autoImplicit false
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ (lpsOriginalAnalyticCosetBranch N hN x) =
      lpsOriginalJDilated N hN (x.out.val⁻¹ • (lpsE2AffineMatrix N hN 0 • τ)) := by
  rw [lpsOriginalAnalyticCosetBranch,lpsOriginalAnalyticCuspAffineBranch_nome]
  exact ((lpsOriginalCosetCuspWitness N hN x).2.property.2.2 τ).symm
end QEC.Coding.TannerLiftedProduct

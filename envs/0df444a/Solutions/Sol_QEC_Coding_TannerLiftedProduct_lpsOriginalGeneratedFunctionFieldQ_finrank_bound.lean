-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_finrank_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:47:48.592727+00:00
-- url     : https://prove2.me/submissions/45777427-c86d-4722-97cd-12fffdc8ee0f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_annihilatorQ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integralQ

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Module.finrank (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)≤
      Nat.card (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [show Module.finrank (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)=
    (minpoly (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN)).natDegree from
      IntermediateField.adjoin.finrank (lpsOriginalJNInFractionField_integralQ N hN)]
  obtain ⟨P,hP,hd,he⟩ := lpsOriginalJNInFractionField_annihilatorQ N hN
  exact (Polynomial.natDegree_le_of_dvd
    (minpoly.dvd (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN) he)
    hP.ne_zero).trans hd
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_finrank_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:41:15.090202+00:00
-- url     : https://prove2.me/submissions/ad5f4cce-530b-4f7f-842f-c3b40c5ecca2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_annihilator
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integral

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    Module.finrank (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN)≤
      Nat.card (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  rw [show Module.finrank (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN)=
    (minpoly (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN)).natDegree from
      IntermediateField.adjoin.finrank (lpsOriginalJNInFractionField_integral N hN)]
  obtain ⟨P,hP,hd,he⟩ := lpsOriginalJNInFractionField_annihilator N hN
  exact (Polynomial.natDegree_le_of_dvd
    (minpoly.dvd (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN) he)
    hP.ne_zero).trans hd
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:38:53.189655+00:00
-- url     : https://prove2.me/submissions/4bad2f9e-040b-49e5-98f4-4d0d52865676

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_annihilator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    IsIntegral (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  obtain ⟨P,hP,_,he⟩ := lpsOriginalJNInFractionField_annihilator N hN
  exact ⟨P,hP,he⟩
end QEC.Coding.TannerLiftedProduct

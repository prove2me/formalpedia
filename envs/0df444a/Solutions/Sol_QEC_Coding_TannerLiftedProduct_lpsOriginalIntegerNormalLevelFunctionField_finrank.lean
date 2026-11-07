-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLevelFunctionField_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:37:55.098004+00:00
-- url     : https://prove2.me/submissions/68338c35-278c-45fe-9c1f-303eab651179

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalLevelFunctionFieldPullback_naturality
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntermediateFieldInclusion_finrank
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_level_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    letI := (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM).toAlgebra
    Module.finrank (lpsOriginalIntegerNormalGluedScheme N hN).functionField
      (lpsOriginalIntegerNormalGluedScheme M hM).functionField =
        (lpsOriginalGeneratedFunctionFieldQ N hN).relfinrank
          (lpsOriginalGeneratedFunctionFieldQ M hM) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let := (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM).toAlgebra
  let := (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom.toAlgebra
  have he : (algebraMap (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ M hM)).comp
        (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom =
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
      (algebraMap (lpsOriginalIntegerNormalGluedScheme N hN).functionField
        (lpsOriginalIntegerNormalGluedScheme M hM).functionField) :=
    (lpsOriginalIntegerNormalLevelFunctionFieldPullback_naturality N M hNM h4N hN hM).symm
  rw [Algebra.finrank_eq_of_equiv_equiv
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN)
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM) he]
  exact lpsOriginalIntermediateFieldInclusion_finrank
    (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalGeneratedFunctionFieldQ M hM)
    (lpsOriginalGeneratedFunctionFieldQ_level_le N M hNM h4N hN hM)
end QEC.Coding.TannerLiftedProduct

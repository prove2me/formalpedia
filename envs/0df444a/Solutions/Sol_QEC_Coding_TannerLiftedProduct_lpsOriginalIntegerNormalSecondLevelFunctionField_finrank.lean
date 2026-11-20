-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSecondLevelFunctionField_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:06:47.364713+00:00
-- url     : https://prove2.me/submissions/24e44883-5f74-422e-8957-2f6af0e2c2d5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalFrickeLevelPullback_finrank
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_naturality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    letI := (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM).toAlgebra
    Module.finrank (lpsOriginalIntegerNormalGluedScheme N hN).functionField
      (lpsOriginalIntegerNormalGluedScheme M hM).functionField =
        (lpsOriginalGeneratedFunctionFieldQ N hN).relfinrank (lpsOriginalGeneratedFunctionFieldQ M hM) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let := (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM).toAlgebra
  let := (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM).toAlgebra
  have he : (algebraMap (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ M hM)).comp
        (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom =
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
      (algebraMap (lpsOriginalIntegerNormalGluedScheme N hN).functionField
        (lpsOriginalIntegerNormalGluedScheme M hM).functionField) :=
    (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_naturality N M hNM h4N hN hM).symm
  rw [Algebra.finrank_eq_of_equiv_equiv
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN)
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM) he]
  exact lpsOriginalRationalFrickeLevelPullback_finrank N M hNM h4N hN hM
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedScheme_stalkIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:16:11.944037+00:00
-- url     : https://prove2.me/submissions/c6ba3a57-a927-4f00-b5bd-b12d8301f568

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.FunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalSchemeChart_stalkIntegrallyClosed
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_cover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_openImmersion


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0<N)
    (x : lpsOriginalIntegerNormalGluedScheme N hN) :
    IsIntegrallyClosed ((lpsOriginalIntegerNormalGluedScheme N hN).presheaf.stalk x) := by
  obtain ⟨b,y,rfl⟩ := lpsOriginalIntegerNormalGluedChartMap_cover N hN x
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN b
  let := lpsOriginalIntegerNormalSchemeChart_stalkIntegrallyClosed N hN b y
  exact IsIntegrallyClosed.of_equiv
    (asIso ((lpsOriginalIntegerNormalGluedChartMap N hN b).stalkMap y)).symm.commRingCatIsoToRingEquiv
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_range_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:39:42.450495+00:00
-- url     : https://prove2.me/submissions/662ea28c-ff81-4ae6-9258-f4e0046b4b06

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_holomorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_nonconstant


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    (Set.range lpsOriginalJInvariant).Infinite := by
  apply (isPreconnected_range lpsOriginalJInvariant_holomorphic.continuous).infinite_of_nontrivial
  by_contra h
  have hs : (Set.range lpsOriginalJInvariant).Subsingleton := Set.not_nontrivial_iff.mp h
  apply lpsOriginalJInvariant_nonconstant
  exact ⟨lpsOriginalJInvariant UpperHalfPlane.I,fun τ => hs ⟨τ,rfl⟩ ⟨UpperHalfPlane.I,rfl⟩⟩
end QEC.Coding.TannerLiftedProduct

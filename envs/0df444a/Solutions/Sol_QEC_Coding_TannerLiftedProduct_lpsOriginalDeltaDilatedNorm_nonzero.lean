-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedNorm_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:47:25.539042+00:00
-- url     : https://prove2.me/submissions/a9403fb1-12f7-43b9-ad2d-1e8d719684dc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDilatedForm_nonzero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalDeltaDilatedNorm N hN≠0 :=
  ModularForm.norm_ne_zero 𝒮ℒ (lpsOriginalDeltaDilatedForm_nonzero N hN)
end QEC.Coding.TannerLiftedProduct

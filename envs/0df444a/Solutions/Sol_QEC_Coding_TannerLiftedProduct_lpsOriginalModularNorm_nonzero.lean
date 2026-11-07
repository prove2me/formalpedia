-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalModularNorm_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:31:31.572389+00:00
-- url     : https://prove2.me/submissions/ee55212c-6aac-4180-881a-7af9210e2df6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularNormInput_nonzero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    lpsOriginalModularNorm N hN c≠0 :=
  ModularForm.norm_ne_zero 𝒮ℒ (lpsOriginalModularNormInput_nonzero N hN c)
end QEC.Coding.TannerLiftedProduct

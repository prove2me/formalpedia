-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalModularNormInput_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:29:38.129081+00:00
-- url     : https://prove2.me/submissions/52564689-1979-4378-baf4-72a761d071cc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDilatedForm_ne_zero_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularNormInput_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_nonconstant


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N) (c : ℂ) :
    (lpsOriginalModularNormInput N hN c:ℍ→ℂ)≠0 := by
  intro h
  apply lpsOriginalJDilated_nonconstant N hN
  refine ⟨c,fun τ => ?_⟩
  have hv := congr_fun h τ
  rw [lpsOriginalModularNormInput_apply] at hv
  have hz : lpsOriginalJDilated N hN τ-c=0 :=
    (mul_eq_zero.mp hv).resolve_left (lpsOriginalDeltaDilatedForm_ne_zero_apply N hN τ)
  exact sub_eq_zero.mp hz
end QEC.Coding.TannerLiftedProduct

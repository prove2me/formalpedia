-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedForm_ne_zero_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:53:44.890813+00:00
-- url     : https://prove2.me/submissions/55650026-dfa6-4444-8816-c38a7243c8ce

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDilatedForm_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalDeltaDilatedForm N hN τ≠0 := by
  rw [lpsOriginalDeltaDilatedForm_apply]
  exact mul_ne_zero (pow_ne_zero 11 (by exact_mod_cast hN.ne'))
    (ModularForm.discriminant_ne_zero _)
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalModularEquationComplex_original_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:31:43.942192+00:00
-- url     : https://prove2.me/submissions/43b02f8f-6429-465f-9b24-4b6dcac31101

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularCosetPolynomial_original_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularEquationComplex_recovery

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) :
    (lpsOriginalModularEquationComplex N hN).eval₂
      (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) (lpsOriginalJDilated N hN τ)=0 := by
  have h := congrArg (fun P : Polynomial ℂ => P.eval (lpsOriginalJDilated N hN τ))
    (lpsOriginalModularEquationComplex_recovery N hN τ)
  rw [Polynomial.eval_mul,Polynomial.eval_C,
    lpsOriginalModularCosetPolynomial_original_root] at h
  rw [Polynomial.eval₂_eq_eval_map]
  exact (mul_eq_zero.mp h).resolve_left
    (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ))
end QEC.Coding.TannerLiftedProduct

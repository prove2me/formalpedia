-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:34:02.859205+00:00
-- url     : https://prove2.me/submissions/4a71819b-6aa0-477b-8269-3c728d259b7b

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even_odd

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R : Type*) [CommRing R] (p : R) (n : ℕ) :
    (lpsHeckePolynomial R p (2 * n)).eval 0 = (-p) ^ n :=
  (lpsHeckePolynomial_eval_zero_even_odd R p n).1
end QEC.Coding.TannerLiftedProduct

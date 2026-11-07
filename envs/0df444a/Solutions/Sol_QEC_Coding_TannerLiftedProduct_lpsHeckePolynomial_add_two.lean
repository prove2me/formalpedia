-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:29:51.535197+00:00
-- url     : https://prove2.me/submissions/da37cd1e-4512-4898-9cbf-48474f9d7eb2

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R : Type*) [CommRing R] (p : R) (n : ℕ) :
    lpsHeckePolynomial R p (n + 2) =
      X * lpsHeckePolynomial R p (n + 1) -
        C p * lpsHeckePolynomial R p n := by
  exact Polynomial.dickson_add_two 2 p n
end QEC.Coding.TannerLiftedProduct

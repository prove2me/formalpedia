-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:29:09.120618+00:00
-- url     : https://prove2.me/submissions/06367151-fbc1-4f9d-bb83-e1318d3d7d9b

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R : Type*) [CommRing R] (p : R) :
    lpsHeckePolynomial R p 0 = 1 := by
  rw [lpsHeckePolynomial, Polynomial.dickson_zero]
  norm_num
end QEC.Coding.TannerLiftedProduct

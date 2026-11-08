-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.re_eval_lpsHeckePolynomial_complex_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:56:35.516211+00:00
-- url     : https://prove2.me/submissions/6f4c007e-d26a-4711-9523-ca830022ff3c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge

set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (x : ℝ) (n : ℕ) :
    Complex.re ((lpsHeckePolynomial ℂ (p : ℂ) n).eval (x : ℂ)) =
      (lpsHeckePolynomial ℝ (p : ℝ) n).eval x := by
  have h : (lpsHeckePolynomial ℂ (p : ℂ) n).eval (x : ℂ) =
      Complex.ofReal ((lpsHeckePolynomial ℝ (p : ℝ) n).eval x) := by
    rw [show lpsHeckePolynomial ℂ (p : ℂ) n =
        (lpsHeckePolynomial ℝ (p : ℝ) n).map Complex.ofRealHom by
      exact (Polynomial.map_dickson
        (k := 2) (a := (p : ℝ)) Complex.ofRealHom n).symm]
    exact Polynomial.eval_map_apply
      (p := lpsHeckePolynomial ℝ (p : ℝ) n) Complex.ofRealHom x
  rw [h, Complex.ofReal_re]
end QEC.Coding.TannerLiftedProduct

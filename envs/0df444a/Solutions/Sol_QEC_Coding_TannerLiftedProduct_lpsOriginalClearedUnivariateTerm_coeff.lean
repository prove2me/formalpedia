-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateTerm_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:22:58.770141+00:00
-- url     : https://prove2.me/submissions/aa8156b4-67d4-4792-91da-f945a5e972e0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N D : ℕ) (K : PowerSeries ℂ) (p : Polynomial ℂ) (i t : ℕ) :
    (PowerSeries.C (p.coeff i)*PowerSeries.X^(N*(D-i))*K^i).coeff t =
      p.coeff i * if N*(D-i)≤t then (K^i).coeff (t-N*(D-i)) else 0 := by
  rw [mul_assoc,PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul']
end QEC.Coding.TannerLiftedProduct

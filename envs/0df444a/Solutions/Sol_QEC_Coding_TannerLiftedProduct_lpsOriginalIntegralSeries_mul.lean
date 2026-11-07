-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralSeries_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:22:40.401196+00:00
-- url     : https://prove2.me/submissions/6089c1a2-5da6-4ae6-b25d-780cc4f2a547

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
theorem _root_.solution (A B : PowerSeries ℂ)
    (hA : ∀ n, IsIntegral ℤ (A.coeff n))
    (hB : ∀ n, IsIntegral ℤ (B.coeff n)) (n : ℕ) :
    IsIntegral ℤ ((A*B).coeff n) := by
  rw [PowerSeries.coeff_mul]
  exact IsIntegral.sum _ (fun i _ => (hA i.1).mul (hB i.2))
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalNomePhase_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:10:45.560406+00:00
-- url     : https://prove2.me/submissions/bf5be26b-245f-43dc-8294-74854fa9028f

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
theorem _root_.solution (r : ℚ) :
    IsIntegral ℤ (Function.Periodic.qParam 1 (r : ℂ)) := by
  change IsIntegral ℤ (Complex.exp (2*Real.pi*I*(r : ℂ)/1))
  rw [div_one]
  exact (Complex.isPrimitiveRoot_exp_rat r).isIntegral r.den_pos
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Gauss_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:50:47.640368+00:00
-- url     : https://prove2.me/submissions/0b22dba9-2d64-4dfb-9514-fe8beb037dab

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_ne_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q))≠0 := by
  apply gaussSum_ne_zero_of_nontrivial
  · rw [ZMod.card]
    exact_mod_cast NeZero.ne q
  · exact lpsQuadraticE2Character_ne_one q hq2
  · exact ZMod.isPrimitive_stdAddChar q
end QEC.Coding.TannerLiftedProduct

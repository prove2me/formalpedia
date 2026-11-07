-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Character_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:49:10.943203+00:00
-- url     : https://prove2.me/submissions/6222a8e6-1491-462b-b3c3-3603ee26a84f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    lpsQuadraticE2Character q≠1 := by
  apply (MulChar.ringHomComp_ne_one_iff (by exact Int.cast_injective)).mpr
  apply quadraticChar_ne_one
  rw [ZMod.ringChar_zmod_n]
  exact hq2
end QEC.Coding.TannerLiftedProduct

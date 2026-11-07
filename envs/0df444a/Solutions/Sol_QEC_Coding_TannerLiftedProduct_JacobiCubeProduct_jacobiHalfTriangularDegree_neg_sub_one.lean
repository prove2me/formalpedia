-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiHalfTriangularDegree_neg_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:14.460202+00:00
-- url     : https://prove2.me/submissions/31a9b5b3-e0f5-4b26-9bb9-c547e873d5c6

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
theorem _root_.solution (z : ℤ) :
    jacobiHalfTriangularDegree (-z - 1) =
      jacobiHalfTriangularDegree z := by
  rw [← Nat.cast_inj (R := ℤ)]
  have h₁ := two_mul_jacobiHalfTriangularDegree (-z - 1)
  have h₂ := two_mul_jacobiHalfTriangularDegree z
  nlinarith
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct

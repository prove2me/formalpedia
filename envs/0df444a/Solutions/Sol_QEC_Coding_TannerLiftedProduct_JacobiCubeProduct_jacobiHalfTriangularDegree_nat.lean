-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiHalfTriangularDegree_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:33:34.702036+00:00
-- url     : https://prove2.me/submissions/47a00cc4-3acf-4700-be47-7f085c347e7b

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
theorem _root_.solution (t : ℕ) :
    jacobiHalfTriangularDegree (t : ℤ) = (t + 1).choose 2 := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_choose_two]
  have h := congrArg (fun z : ℤ => (z : ℚ))
    (two_mul_jacobiHalfTriangularDegree (t : ℤ))
  push_cast at h ⊢
  nlinarith
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct

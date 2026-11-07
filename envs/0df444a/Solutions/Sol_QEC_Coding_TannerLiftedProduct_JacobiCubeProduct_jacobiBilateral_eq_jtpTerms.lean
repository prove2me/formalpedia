-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiBilateral_eq_jtpTerms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:33:09.93665+00:00
-- url     : https://prove2.me/submissions/8369e21a-77cd-4c5d-bef0-6acd54b2cb67

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
theorem _root_.solution :
    jacobiBilateral =
      (∑' n : ℕ, jtpPositiveTerm n) + ∑' n : ℕ, jtpNegativeTerm n := by
  rw [jacobiBilateral]
  congr 1
  apply tsum_congr
  intro m
  rw [jtpNegativeTerm]
  congr 3
  ring
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct

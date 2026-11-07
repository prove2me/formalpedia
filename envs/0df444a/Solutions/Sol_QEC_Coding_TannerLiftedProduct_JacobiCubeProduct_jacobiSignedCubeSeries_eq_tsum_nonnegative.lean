-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiSignedCubeSeries_eq_tsum_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:50:30.551096+00:00
-- url     : https://prove2.me/submissions/4760498a-cc79-4c6d-aa86-371a304de26e

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiSignedCubeSeries_eq_tsum_signedTriangularTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_tsum_signedTriangularTerm_eq_two_mul_nonnegative

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
theorem _root_.solution :
    jacobiSignedCubeSeries =
      ∑' n : ℕ, signedTriangularTerm (n : ℤ) := by
  rw [jacobiSignedCubeSeries_eq_tsum_signedTriangularTerm,
    tsum_signedTriangularTerm_eq_two_mul_nonnegative]
  change PowerSeries.C (1 / 2 : ℚ) *
      ((PowerSeries.C 2) * ∑' n : ℕ, signedTriangularTerm (n : ℤ)) = _
  rw [← mul_assoc, ← map_mul]
  norm_num
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct

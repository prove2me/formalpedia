-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiThetaProduct_eq_rationalIntegerThetaSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:25:05.155268+00:00
-- url     : https://prove2.me/submissions/fb709830-58fe-46cc-ad17-c2427bc242de

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_lhs
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_rhs
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_jacobi_triple_product


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiThetaProduct = rationalIntegerThetaSeries := by
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  letI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := JacobiTripleProductCore.piTop
  have h := congrArg jacobiPowerSeriesEvalOne
    JacobiTripleProductCore.jacobi_triple_product
  rw [jacobiPowerSeriesEvalOne_lhs,
    jacobiPowerSeriesEvalOne_rhs] at h
  exact h
end QEC.Coding.TannerLiftedProduct

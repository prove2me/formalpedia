-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalThetaLevel_filled_isManifold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:04:36.736534+00:00
-- url     : https://prove2.me/submissions/01fb8d4e-d14b-46f4-9b83-163b3703b96c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : q≠0) :
    let : NeZero ((4*q)^2) := ⟨by positivity⟩
    letI := lpsOriginalFilledTopology ((4*q)^2)
    letI := lpsOriginalFilledChartedSpace ((4*q)^2)
      (dvd_pow (dvd_mul_right 4 q) (by decide))
    IsManifold 𝓘(ℂ) ω (LPSOriginalFilledCurve ((4*q)^2)) := by
  let : NeZero ((4*q)^2) := ⟨by positivity⟩
  exact lpsOriginalFilled_isManifold ((4*q)^2)
    (dvd_pow (dvd_mul_right 4 q) (by decide))
end QEC.Coding.TannerLiftedProduct

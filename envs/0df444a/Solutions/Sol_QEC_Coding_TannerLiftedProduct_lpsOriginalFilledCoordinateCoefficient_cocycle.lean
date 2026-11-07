-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCoordinateCoefficient_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:01:02.844203+00:00
-- url     : https://prove2.me/submissions/97fe6bed-da78-46e5-a573-d75bccee4a4b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_interior_cusp_differential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_cusp_interior_differential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_cusp_cusp_differential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_interior_interior_differential

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x y : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈((chartAt ℂ x).symm.trans (chartAt ℂ y)).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    let e := (chartAt ℂ x).symm.trans (chartAt ℂ y)
    lpsOriginalFilledCoordinateCoefficient N f y (e z) * deriv e z =
      lpsOriginalFilledCoordinateCoefficient N f x z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  cases x with
  | inl x =>
    cases y with
    | inl y => exact lpsOriginalFilled_interior_interior_differential N hN f x y z hz
    | inr c => exact lpsOriginalFilled_interior_cusp_differential N hN f x c z hz
  | inr c =>
    cases y with
    | inl x => exact lpsOriginalFilled_cusp_interior_differential N hN f x c z hz
    | inr d => exact lpsOriginalFilled_cusp_cusp_differential N f c d z hz
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaSquareMean_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:32:39.451286+00:00
-- url     : https://prove2.me/submissions/e17f958e-6638-4d91-bdd4-8fb557d75cb3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaSquareMean
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleSquareMean_hasSum


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (y : ℝ) (hy : 0<y) :
    HasSum (fun n : ℕ => (lpsThetaSquareCoeff q hq4 n:ℂ)*
      (Real.exp (-(4*Real.pi*(n:ℝ))*y):ℂ)) (lpsThetaSquareMean q hq4 y:ℂ) :=
  lpsCuspHorocycleSquareMean_hasSum _ _ _ hy
end QEC.Coding.TannerLiftedProduct

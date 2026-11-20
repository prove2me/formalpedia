-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCenteredThetaResidual_even_eq_hecke_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:04:29.58578+00:00
-- url     : https://prove2.me/submissions/6dc3f60a-4fc2-4618-b1bd-37e8c6f7ce33

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_one_lpsThetaHeckePrimePower
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredThetaResidual_even_eq_cuspidal_coefficient


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ)
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredThetaResidual a (2*n)=
      (Fintype.card PSL(2,ZMod a.q):ℝ)*
        (PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1
          (lpsThetaHeckePrimePower p a (2*n)))).re+2*(-(p:ℝ))^n := by
  rw [coeff_one_lpsThetaHeckePrimePower]
  exact lpsCenteredThetaResidual_even_eq_cuspidal_coefficient p a n
end QEC.Coding.TannerLiftedProduct

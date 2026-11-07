-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:12:51.157989+00:00
-- url     : https://prove2.me/submissions/0626476a-7cbd-46aa-8335-0a5c207bed9d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_add_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (z : ℍ) :
    lpsChi4E2Twist ((1:ℝ) +ᵥ z)=lpsChi4E2Twist z := by
  unfold lpsChi4E2Twist
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [show ((a.val:ℝ)/(4:ℝ)) +ᵥ ((1:ℝ) +ᵥ z) =
    (1:ℝ) +ᵥ (((a.val:ℝ)/(4:ℝ)) +ᵥ z) by
      rw [← add_vadd,← add_vadd,add_comm],lpsE2_add_one]
end QEC.Coding.TannerLiftedProduct

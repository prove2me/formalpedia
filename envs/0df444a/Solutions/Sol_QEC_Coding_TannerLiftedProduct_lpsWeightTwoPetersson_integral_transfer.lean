-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoPetersson_integral_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:51:15.445124+00:00
-- url     : https://prove2.me/submissions/0d7ac2d8-eeac-499a-a96b-7dd511973a31

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoPetersson_transfer

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (f g : ℍ → ℂ) (A : GL (Fin 2) ℝ)
    (hA : 0 < A.det.val) (s : Set ℍ) :
    (∫τ in s,petersson 2 (f ∣[(2 : ℤ)] A) g τ) =
      ∫τ in A • s,petersson 2 f (g ∣[(2 : ℤ)] A⁻¹) τ := by
  simp_rw [lpsWeightTwoPetersson_transfer f g A hA]
  exact ((measurePreserving_smul A volume).setIntegral_image_emb
    (measurableEmbedding_const_smul A) (petersson 2 f (g ∣[(2 : ℤ)] A⁻¹)) s).symm
end QEC.Coding.TannerLiftedProduct

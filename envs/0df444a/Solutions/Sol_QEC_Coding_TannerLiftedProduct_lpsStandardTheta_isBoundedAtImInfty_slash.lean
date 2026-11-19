-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsStandardTheta_isBoundedAtImInfty_slash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:31:35.764809+00:00
-- url     : https://prove2.me/submissions/ee65de03-b5d4-47d2-9e26-f11eee6642f1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_tendsto_lpsStandardTheta_slash

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0<q) (γ : SL(2,ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) := by
  obtain ⟨v,hv⟩ := exists_tendsto_lpsStandardTheta_slash q hq γ
  exact hv.isBigO_one ℝ
end QEC.Coding.TannerLiftedProduct

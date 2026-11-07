-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_S_not_zero_at_infty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:56:59.095098+00:00
-- url     : https://prove2.me/submissions/0e67e026-5839-4721-8f54-46fb2c63a208

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tendsto_lpsStandardTheta_slash_S

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0 < q) :
    ¬ UpperHalfPlane.IsZeroAtImInfty
      ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2 : ℤ)] ModularGroup.S) := by
  intro h
  have he := tendsto_nhds_unique (tendsto_lpsStandardTheta_slash_S q hq) h
  have qn : (q:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  exact (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 qn)))) he
end QEC.Coding.TannerLiftedProduct

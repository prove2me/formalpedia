-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0CosetSection_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:55:59.123127+00:00
-- url     : https://prove2.me/submissions/b3b56a1f-5283-41d7-95a1-7d9fdba5f5cb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveGamma0CosetEquiv_mk

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (c : lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N) :
    QuotientGroup.mk (lpsGamma0CosetSection N c) = c := by
  have he := lpsEffectiveGamma0CosetEquiv_mk N (Quotient.out ((lpsEffectiveGamma0CosetEquiv N).symm c))
  have hh := congrArg (lpsEffectiveGamma0CosetEquiv N)
    (Quotient.out_eq' ((lpsEffectiveGamma0CosetEquiv N).symm c))
  exact he.symm.trans (hh.trans ((lpsEffectiveGamma0CosetEquiv N).apply_symm_apply c))
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0PeterssonDomain_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:57:37.623112+00:00
-- url     : https://prove2.me/submissions/f1eeb960-c941-4c52-8474-6f0046a21b00

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0CosetSection_mk
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_fundamental


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) :
    IsFundamentalDomain (lpsEffectiveGamma0 N) (lpsGamma0PeterssonDomain N) volume :=
  lpsCosetSectionDomain_fundamental _ _ (lpsGamma0CosetSection_mk N)
end QEC.Coding.TannerLiftedProduct

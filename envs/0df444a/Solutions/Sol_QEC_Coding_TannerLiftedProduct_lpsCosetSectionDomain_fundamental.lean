-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:54:44.350086+00:00
-- url     : https://prove2.me/submissions/9f7235c9-7bea-446b-8ee6-4d807bf0c9e5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_nullMeasurable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_covers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_aedisjoint

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) :
    IsFundamentalDomain H (lpsCosetSectionDomain H r) volume := by
  apply IsFundamentalDomain.mk'' (lpsCosetSectionDomain_nullMeasurable H r)
  · exact Eventually.of_forall (lpsCosetSectionDomain_covers H r hr)
  · exact lpsCosetSectionDomain_aedisjoint H r hr
  · intro h
    exact (lpsEffectiveMeasurePreserving (h : lpsEffectiveModularGroup)).quasiMeasurePreserving
end QEC.Coding.TannerLiftedProduct

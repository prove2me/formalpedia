-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_nullMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:52:34.538948+00:00
-- url     : https://prove2.me/submissions/2184853b-f754-43b3-ba03-d473fce34173

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveCosets_countable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveFundamentalDomain


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup) :
    NullMeasurableSet (lpsCosetSectionDomain H r) volume := by
  letI : Countable (lpsEffectiveModularGroup ⧸ H) := lpsEffectiveCosets_countable H
  apply NullMeasurableSet.iUnion
  intro c
  exact lpsEffectiveFundamentalDomain.nullMeasurableSet_smul (r c)⁻¹
end QEC.Coding.TannerLiftedProduct

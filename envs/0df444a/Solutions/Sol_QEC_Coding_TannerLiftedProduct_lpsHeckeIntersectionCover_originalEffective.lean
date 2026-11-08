-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionCover_originalEffective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:09:27.494196+00:00
-- url     : https://prove2.me/submissions/32599b10-eb3a-4456-a047-ab21a4f2f40c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersectionCover_fundamental
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_product_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeFundamental_subgroupOf


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) {s : Set ℍ}
    (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain (lpsEffectiveGamma0 (N*p))
      (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • s) volume := by
  have hle : lpsEffectiveGamma0 (N*p) ≤ lpsEffectiveGamma0 N :=
    Subgroup.map_mono (lpsGamma0_product_le N p)
  exact lpsRelativeFundamental_subgroupOf _ _ hle (lpsHeckeIntersectionCover_fundamental N p hNp hs)
end QEC.Coding.TannerLiftedProduct

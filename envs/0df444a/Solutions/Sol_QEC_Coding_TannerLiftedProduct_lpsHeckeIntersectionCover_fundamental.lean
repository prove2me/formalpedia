-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionCover_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:07:47.73561+00:00
-- url     : https://prove2.me/submissions/cd2528b2-2a32-42ba-99ff-61f79a351620

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersectionEffectiveRepresentative_mk
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIndexedRelativeDomain_fundamental


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain ((lpsEffectiveGamma0 (N*p)).subgroupOf (lpsEffectiveGamma0 N))
      (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • s) volume :=
  lpsIndexedRelativeDomain_fundamental _ s hs
    (lpsEffectiveHeckeIntersectionCosetEquiv N p hNp).symm _
    (lpsHeckeIntersectionEffectiveRepresentative_mk N p hNp)
end QEC.Coding.TannerLiftedProduct

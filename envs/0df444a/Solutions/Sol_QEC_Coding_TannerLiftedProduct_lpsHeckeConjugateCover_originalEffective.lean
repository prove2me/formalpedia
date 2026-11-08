-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateCover_originalEffective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:09:42.218468+00:00
-- url     : https://prove2.me/submissions/b903d0f6-cade-414e-bb9f-38efe74c1a83

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateCover_fundamental
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
    IsFundamentalDomain (lpsEffectiveHeckeConjugateIntersection N p)
      (⋃i,(lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • s) volume := by
  have hle : lpsEffectiveHeckeConjugateIntersection N p ≤ lpsEffectiveGamma0 N :=
    Subgroup.map_mono (show lpsHeckeConjugateIntersection N p ≤ CongruenceSubgroup.Gamma0 N from inf_le_left)
  exact lpsRelativeFundamental_subgroupOf _ _ hle (lpsHeckeConjugateCover_fundamental N p hNp hs)
end QEC.Coding.TannerLiftedProduct

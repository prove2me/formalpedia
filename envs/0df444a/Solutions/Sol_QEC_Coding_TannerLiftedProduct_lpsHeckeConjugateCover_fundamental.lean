-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateCover_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:08:04.431632+00:00
-- url     : https://prove2.me/submissions/a0249fbf-b0f8-46ee-96c7-e32f58ab1193

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateEffectiveRepresentative_mk
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIndexedRelativeDomain_fundamental


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain ((lpsEffectiveHeckeConjugateIntersection N p).subgroupOf (lpsEffectiveGamma0 N))
      (⋃i,(lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • s) volume :=
  lpsIndexedRelativeDomain_fundamental _ s hs
    (lpsEffectiveHeckeConjugateCosetEquiv N p hNp).symm _
    (lpsHeckeConjugateEffectiveRepresentative_mk N p hNp)
end QEC.Coding.TannerLiftedProduct

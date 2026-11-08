-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeLeftImageCover_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:11:23.051637+00:00
-- url     : https://prove2.me/submissions/9d7a7af8-81f4-4c32-8542-38be17314f28

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveFundamental_perm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPermConjugateFundamental
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugatePerm_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveFundamental_of_perm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersectionCover_originalEffective


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
      (lpsHeckeUpperGL ℝ p none •
        (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • s)) volume := by
  have hA := lpsHeckeIntersectionCover_originalEffective N p hNp hs
  have hP := lpsEffectiveFundamental_perm _ hA
  have hC := lpsPermConjugateFundamental _ (lpsHeckeUpperGL ℝ p none) hP
  rw [←lpsHeckeConjugatePerm_eq N p] at hC
  exact lpsEffectiveFundamental_of_perm _ hC
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToSpecZ_flat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:08:17.41599+00:00
-- url     : https://prove2.me/submissions/6e8e8aea-5503-4358-b6f9-404637746f43

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroChart_intFlat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalInfinityChart_intFlat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerSpecZ_hom_unique


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0 < N) :
    Flat (lpsOriginalIntegerNormalGluedToSpecZ N hN) := by
  let : IsZariskiLocalAtSource (@AlgebraicGeometry.Flat.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Flat.{0})
      (Q := @RingHom.Flat.{0, 0})
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Flat.{0})
    (f := lpsOriginalIntegerNormalGluedToSpecZ N hN)
    (lpsOriginalIntegerNormalSchemeGlueData N hN).openCover).mpr
  intro b
  change Flat (lpsOriginalIntegerNormalGluedChartMap N hN b ≫
    lpsOriginalIntegerNormalGluedToSpecZ N hN)
  cases b with
  | false =>
    have hm := lpsOriginalIntegerSpecZ_hom_unique
      (lpsOriginalIntegerNormalZeroChart N hN)
      (lpsOriginalIntegerNormalGluedChartMap N hN false ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN)
      (Spec.map (CommRingCat.ofHom (Int.castRingHom (lpsOriginalIntegerNormalZeroChart N hN))))
    exact hm.symm ▸ Flat.SpecMap_iff.mpr
      (lpsOriginalIntegerNormalZeroChart_intFlat N hN)
  | true =>
    have hm := lpsOriginalIntegerSpecZ_hom_unique
      (lpsOriginalIntegerNormalInfinityChart N hN)
      (lpsOriginalIntegerNormalGluedChartMap N hN true ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN)
      (Spec.map (CommRingCat.ofHom (Int.castRingHom (lpsOriginalIntegerNormalInfinityChart N hN))))
    exact hm.symm ▸ Flat.SpecMap_iff.mpr
      (lpsOriginalIntegerNormalInfinityChart_intFlat N hN)
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedScheme_noetherian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:16:08.515463+00:00
-- url     : https://prove2.me/submissions/c0cf3fc6-0372-4c0a-bf97-09a47954c0dd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalSchemeChart_locallyNoetherian

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0<N) :
    IsNoetherian (lpsOriginalIntegerNormalGluedScheme N hN) := by
  let D := lpsOriginalIntegerNormalSchemeGlueData N hN
  let : ∀ b : D.openCover.I₀, CompactSpace (D.openCover.X b) := fun b => by
    cases b with
    | false => exact Scheme.compactSpace_of_isAffine (Spec (.of (lpsOriginalIntegerNormalZeroChart N hN)))
    | true => exact Scheme.compactSpace_of_isAffine (Spec (.of (lpsOriginalIntegerNormalInfinityChart N hN)))
  let : Finite D.openCover.I₀ := inferInstanceAs (Finite Bool)
  have hc : CompactSpace D.glued := D.openCover.compactSpace
  have hn : IsLocallyNoetherian D.glued :=
    (isLocallyNoetherian_iff_openCover D.openCover).mpr
      (lpsOriginalIntegerNormalSchemeChart_locallyNoetherian N hN)
  exact { toIsLocallyNoetherian := hn, toCompactSpace := hc }
end QEC.Coding.TannerLiftedProduct

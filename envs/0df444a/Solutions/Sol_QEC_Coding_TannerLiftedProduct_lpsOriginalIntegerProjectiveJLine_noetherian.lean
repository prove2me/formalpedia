-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJLine_noetherian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:58:46.953671+00:00
-- url     : https://prove2.me/submissions/b417d5d9-2de6-4860-8e8d-990e19600bfa

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    IsNoetherian lpsOriginalIntegerProjectiveJLine := by
  let D := lpsOriginalIntegerProjectiveJGlueData
  let : ∀ b : D.openCover.I₀, CompactSpace (D.openCover.X b) :=
    fun _ => Scheme.compactSpace_of_isAffine (Spec (.of (Polynomial ℤ)))
  let : Finite D.openCover.I₀ := inferInstanceAs (Finite Bool)
  have hc : CompactSpace D.glued := D.openCover.compactSpace
  have hn : IsLocallyNoetherian D.glued :=
    (isLocallyNoetherian_iff_openCover D.openCover).mpr
      (fun _ => inferInstanceAs (IsLocallyNoetherian (Spec (.of (Polynomial ℤ)))))
  exact { toIsLocallyNoetherian := hn, toCompactSpace := hc }
end QEC.Coding.TannerLiftedProduct

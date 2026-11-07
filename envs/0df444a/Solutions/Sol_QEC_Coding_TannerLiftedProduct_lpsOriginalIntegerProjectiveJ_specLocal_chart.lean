-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJ_specLocal_chart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:53:37.827192+00:00
-- url     : https://prove2.me/submissions/1fbca962-0bda-4938-b759-6e10d3fd45e9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJChartMap_openImmersion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJChartMap_cover

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R : Type) [CommRing R] [IsLocalRing R]
    (f : Spec (.of R) ⟶ lpsOriginalIntegerProjectiveJLine) :
    ∃ (b : Bool) (g : Spec (.of R) ⟶ Spec (.of (Polynomial ℤ))),
      g ≫ lpsOriginalIntegerProjectiveJChartMap b = f := by
  obtain ⟨b,y,hy⟩ := lpsOriginalIntegerProjectiveJChartMap_cover
    (f (IsLocalRing.closedPoint R))
  let := lpsOriginalIntegerProjectiveJChartMap_openImmersion b
  let U : TopologicalSpace.Opens (PrimeSpectrum R) :=
    f ⁻¹ᵁ (lpsOriginalIntegerProjectiveJChartMap b).opensRange
  have hU : U=⊤ := (IsLocalRing.closedPoint_mem_iff U).mp ⟨y,hy⟩
  have hr : Set.range f ⊆ Set.range (lpsOriginalIntegerProjectiveJChartMap b) := by
    rintro x ⟨x,rfl⟩
    have hx : x ∈ U := by rw [hU]; trivial
    exact hx
  exact ⟨b,IsOpenImmersion.lift (lpsOriginalIntegerProjectiveJChartMap b) f hr,
    IsOpenImmersion.lift_fac _ _ _⟩
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:20.524368+00:00
-- url     : https://prove2.me/submissions/a16fad40-38d7-42bf-800b-2f8877719cd0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R₀ : Type} [CommRing R₀]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution [IsLocalRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] :
    Nonempty (Chart G) := by
  obtain ⟨U, hU, hmem, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := (η[G]).left.base (IsLocalRing.closedPoint R₀)) (U := ⊤) (by trivial)
  refine ⟨⟨U, hU, ?_⟩⟩
  intro y _
  exact (IsLocalRing.specializes_closedPoint (R := R₀) y).mem_open ((η[G]).left ⁻¹ᵁ U).isOpen hmem
end ReciprocityTheory.ChartRestriction.G.Chart

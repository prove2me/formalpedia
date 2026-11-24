-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.chart_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:49.322056+00:00
-- url     : https://prove2.me/submissions/5566ee3a-afab-43c9-8cfa-971c88769f6f

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
variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] (C : Chart G)
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution [Smooth G.hom] : Algebra.Smooth R₀ Γ(G.left, C.U) := by
  have h1 : Smooth (C.hU.fromSpec ≫ G.hom) := inferInstance
  rw [fromSpec_over] at h1
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h1
end ReciprocityTheory.ChartRestriction.G.Chart

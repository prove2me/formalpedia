-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.spMap_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:44.30309+00:00
-- url     : https://prove2.me/submissions/224f6141-e409-4a08-853b-d8c01c87f2d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_left

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
variable (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
variable {G}
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (C : Chart G) {P P' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P']
    (g : P →ₐ[R₀] P') (h : Γ(G.left, C.U) →ₐ[R₀] P) : spMap g ≫ pt C h = pt C (g.comp h) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, spMap_left, pt_left, pt_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl
end ReciprocityTheory.ChartRestriction.G.Chart

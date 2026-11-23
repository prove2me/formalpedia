-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.pt_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:44.374785+00:00
-- url     : https://prove2.me/submissions/5b2a7c9b-8a23-471a-bdae-0349904f2ee9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
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
theorem _root_.solution (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] {h h' : Γ(G.left, C.U) →ₐ[R₀] P}
    (H : pt C h = pt C h') : h = h' := by
  have h1 : (pt C h).left = (pt C h').left := by rw [H]
  rw [pt_left, pt_left] at h1
  have h2 := (cancel_mono C.hU.fromSpec).mp h1
  have h3 := Spec.map_injective h2
  apply AlgHom.ext
  intro a
  exact congrArg (fun f => f.hom a) h3
end ReciprocityTheory.ChartRestriction.G.Chart

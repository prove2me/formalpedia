-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.pt_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:38:38.981105+00:00
-- url     : https://prove2.me/submissions/8e5e7b7e-b845-4715-b054-8563f00c9cbc

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
variable (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
variable {G}
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] (h : Γ(G.left, C.U) →ₐ[R₀] P) :
    (pt C h).left = Spec.map (CommRingCat.ofHom h.toRingHom) ≫ C.hU.fromSpec := rfl
end ReciprocityTheory.ChartRestriction.G.Chart

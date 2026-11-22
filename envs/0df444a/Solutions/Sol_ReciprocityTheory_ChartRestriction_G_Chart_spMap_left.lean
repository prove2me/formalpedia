-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.spMap_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:04.84187+00:00
-- url     : https://prove2.me/submissions/6bd6d2de-7ab1-44e7-bed8-d4db59647a85

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
theorem _root_.solution {P P' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P'] (g : P →ₐ[R₀] P') :
    (spMap g).left = Spec.map (CommRingCat.ofHom g.toRingHom) := rfl
end ReciprocityTheory.ChartRestriction.G.Chart

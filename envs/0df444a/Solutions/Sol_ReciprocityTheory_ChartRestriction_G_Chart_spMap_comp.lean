-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:41:27.421573+00:00
-- url     : https://prove2.me/submissions/edbf2fa4-a870-4764-aec6-4dc53b410b1c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

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
theorem _root_.solution {P P' P'' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P']
    [CommRing P''] [Algebra R₀ P''] (g : P →ₐ[R₀] P') (g' : P' →ₐ[R₀] P'') :
    spMap g' ≫ spMap g = spMap (R₀ := R₀) (g'.comp g) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, spMap_left, spMap_left, spMap_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl
end ReciprocityTheory.ChartRestriction.G.Chart

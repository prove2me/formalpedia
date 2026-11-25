-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.res_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:31:41.881875+00:00
-- url     : https://prove2.me/submissions/bc794b45-9323-4147-b415-c611caae4f18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dualMapS_comp_scaleS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp


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
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S]
variable {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (j : A →ₐ[S] A') (c : A)
    (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (dualMapS j) ≫ spMap (scaleS c) ≫ y = spMap (scaleS (j c)) ≫ spMap (dualMapS j) ≫ y := by
  rw [← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, dualMapS_comp_scaleS]
end ReciprocityTheory.ChartRestriction.G.Chart

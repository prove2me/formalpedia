-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.pushR_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:10.234497+00:00
-- url     : https://prove2.me/submissions/30f3b440-3adc-466a-8e54-7ee040d26a31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_left


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]
    (y : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) (e : G ⟶ G) :
    pushR G (y ≫ (Over.pullback (fB R R')).map e) = pushR G y ≫ e := by
  apply Over.OverMorphism.ext
  rw [pushR_left, Over.comp_left, Over.comp_left, pushR_left, Category.assoc, Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _
end ReciprocityTheory.ChartRestriction.G.Chart

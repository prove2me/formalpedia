-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.lift_one_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:47.886909+00:00
-- url     : https://prove2.me/submissions/33cce4af-ba57-431e-8d9f-77a1cf40f3ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExtVCat

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution : lift (1 : 𝟙_ (Over S) ⟶ G) (lift (1 : 𝟙_ (Over S) ⟶ G) 1) = (1 : 𝟙_ (Over S) ⟶ G3 G) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, MonObj.one_comp]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_snd, lift_fst, Category.assoc, MonObj.one_comp]
    · rw [lift_snd, lift_snd, Category.assoc, MonObj.one_comp]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor

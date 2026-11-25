-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.JGPf.ext_of_fromSpecStalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:38:11.208914+00:00
-- url     : https://prove2.me/submissions/e019b903-8105-4afe-b9c5-66dbe62f309f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_JGPf_specMap_stalkCongr

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
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.JGPf
universe u
set_option maxHeartbeats 1000000
namespace ReciprocityTheory.ChartRestriction.G.TB.JGPf
theorem _root_.solution {Y X : Scheme.{u}} (f g : Y ⟶ X)
    (h : ∀ y, Y.fromSpecStalk y ≫ f = Y.fromSpecStalk y ≫ g) : f = g := by
  have hb : ∀ y, f y = g y := fun y => by
    have := congr($(h y) (IsLocalRing.closedPoint (Y.presheaf.stalk y)))
    change f (Y.fromSpecStalk y (IsLocalRing.closedPoint _)) = g (Y.fromSpecStalk y (IsLocalRing.closedPoint _)) at this
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  have hbase : f.base = g.base := by ext y; exact hb y
  have hs : ∀ y, f.stalkMap y = (X.presheaf.stalkCongr (Inseparable.of_eq (hb y))).hom ≫ g.stalkMap y := by
    intro y
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (f y))]
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc, specMap_stalkCongr (hb y),
      Scheme.SpecMap_stalkMap_fromSpecStalk, h y]
  refine Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' ?_)
  have := SheafedSpace.hom_stalk_ext _ _ hbase hs
  exact congrArg InducedCategory.Hom.hom this
end ReciprocityTheory.ChartRestriction.G.TB.JGPf

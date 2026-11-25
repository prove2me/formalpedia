-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.eig_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:48:08.184255+00:00
-- url     : https://prove2.me/submissions/c3213d77-298d-4a47-8ee7-fe5bc191e2c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_eq_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_act
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_pre


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
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : Geo.Tor.IsGrpPullback G' G f F) {k : Type} [Field k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)
include hc
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (a : G' ⟶ G') (b : G ⟶ G) (hab : a.left ≫ F = F ≫ b.left) (s : k)
    {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    (w ≫ a).left = Geo.Tor.spMap (Geo.Tor.epsScale s) ≫ w.left ↔ v ≫ (Over.pullback g).map b = spMap (scaleD s) ≫ v := by
  rw [← rel_eq_iff hc (rel_act a b hab h) (rel_pre (spMap (scaleD s)) h)]
  constructor
  · intro e
    exact Over.OverMorphism.ext e
  · intro e
    exact congrArg (fun q => q.left) e
end ReciprocityTheory.ChartRestriction.G.Chart

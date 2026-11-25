-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.rel_exists_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:10:45.559813+00:00
-- url     : https://prove2.me/submissions/459bc3b5-7fa2-4050-8489-81b0f1730041

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : IsGrpPullback G' G f F) {k : Type} [Field k] (tk : Spec (CommRingCat.of k) ⟶ S') (g : Spec (CommRingCat.of k) ⟶ S)
  (hg : tk ≫ f = g)
variable {tk g}
include hc hg
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {X : Over (Spec (CommRingCat.of k))} (v : X ⟶ (Over.pullback g).obj G) :
    ∃ w : viaT tk X ⟶ G', Rel (F := F) tk g w v := by
  have hv : v.left ≫ pullback.snd G.hom g = X.hom := Over.w v
  refine ⟨Over.homMk (hc.1.lift (v.left ≫ pullback.fst G.hom g) (X.hom ≫ tk) ?_) ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hv, Category.assoc, hg]
  · exact hc.1.lift_snd _ _ _
  · exact hc.1.lift_fst _ _ _
end ReciprocityTheory.ChartRestriction.G.Chart

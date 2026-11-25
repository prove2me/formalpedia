-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.rel_exists_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:26:31.032858+00:00
-- url     : https://prove2.me/submissions/fe54c73b-a65b-4d2e-9e14-a0e536d9724a

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
theorem _root_.solution {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') :
    ∃ v : X ⟶ (Over.pullback g).obj G, Rel (F := F) tk g w v := by
  have hw : w.left ≫ G'.hom = X.hom ≫ tk := Over.w w
  refine ⟨Over.homMk (pullback.lift (w.left ≫ F) X.hom ?_) ?_, ?_⟩
  · rw [Category.assoc, hc.1.w, ← Category.assoc, hw, Category.assoc, hg]
  · exact pullback.lift_snd _ _ _
  · exact (pullback.lift_fst _ _ _).symm
end ReciprocityTheory.ChartRestriction.G.Chart

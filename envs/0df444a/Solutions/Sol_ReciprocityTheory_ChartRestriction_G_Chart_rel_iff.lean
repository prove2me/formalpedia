-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.rel_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:55:21.619896+00:00
-- url     : https://prove2.me/submissions/b205ff9c-62ce-40d7-9bd9-fda20acf1547

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


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
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) :
    Rel (F := F) tk g w v ↔
      pushPt (isGrpPullback_pullback G g).1.w v = iota2 hg X ≫ pushPt hc.1.w w := by
  constructor
  · intro h
    apply Over.OverMorphism.ext
    show v.left ≫ pullback.fst G.hom g = 𝟙 _ ≫ w.left ≫ F
    rw [Category.id_comp]
    exact h.symm
  · intro h
    have h2 : v.left ≫ pullback.fst G.hom g = 𝟙 _ ≫ w.left ≫ F := congrArg (fun u => u.left) h
    rw [Category.id_comp] at h2
    exact h2.symm
end ReciprocityTheory.ChartRestriction.G.Chart

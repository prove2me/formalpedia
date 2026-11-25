-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.rel_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:26:06.373843+00:00
-- url     : https://prove2.me/submissions/22c8c770-5a45-4f25-9732-1cd660583b71

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_iff
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
include hc hg
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v') : Rel (F := F) tk g (w * w') (v * v') := by
  have e := (rel_iff hc hg w v).1 h
  have e' := (rel_iff hc hg w' v').1 h'
  have h1 := (isGrpPullback_pullback G g).2 X v v' (pushPt (isGrpPullback_pullback G g).1.w v)
    (pushPt (isGrpPullback_pullback G g).1.w v') rfl rfl
  have h2 := hc.2 (viaT tk X) w w' (pushPt hc.1.w w) (pushPt hc.1.w w') rfl rfl
  show (w * w').left ≫ F = (v * v').left ≫ pullback.fst G.hom g
  rw [← h1, ← h2, e, e', CategoryTheory.Hom.mul_def, CategoryTheory.Hom.mul_def, ← comp_lift,
    Category.assoc]
  exact (Category.id_comp _).symm
end ReciprocityTheory.ChartRestriction.G.Chart

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.rel_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:36:52.986453+00:00
-- url     : https://prove2.me/submissions/a7cb2cbb-38dd-4282-85e0-4ccbeca08d2b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one___d94ad01bda45
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
theorem _root_.solution {X : Over (Spec (CommRingCat.of k))} : Rel (F := F) tk g (1 : viaT tk X ⟶ G') (1 : X ⟶ (Over.pullback g).obj G) := by
  have p1 : ∀ {T : Over S'} {T' : Over S} (e : T' ⟶ Over.mk (T.hom ≫ f)),
      e ≫ pushPt hc.1.w (1 : T ⟶ G') = 1 := by
    intro T T' e
    have hm := hc.2 T 1 1 (pushPt hc.1.w (1 : T ⟶ G')) (pushPt hc.1.w (1 : T ⟶ G')) rfl rfl
    rw [_root_.mul_one] at hm
    have hp : pushPt hc.1.w (1 : T ⟶ G') * pushPt hc.1.w (1 : T ⟶ G') = pushPt hc.1.w (1 : T ⟶ G') :=
      Over.OverMorphism.ext hm
    rw [mul_eq_left] at hp
    rw [hp, comp_one'']
  have p2 : pushPt (isGrpPullback_pullback G g).1.w (1 : X ⟶ (Over.pullback g).obj G) = 1 := by
    have hm := (isGrpPullback_pullback G g).2 X 1 1 (pushPt (isGrpPullback_pullback G g).1.w 1)
      (pushPt (isGrpPullback_pullback G g).1.w 1) rfl rfl
    rw [_root_.mul_one] at hm
    have hp : pushPt (isGrpPullback_pullback G g).1.w (1 : X ⟶ (Over.pullback g).obj G) *
        pushPt (isGrpPullback_pullback G g).1.w (1 : X ⟶ (Over.pullback g).obj G) =
        pushPt (isGrpPullback_pullback G g).1.w (1 : X ⟶ (Over.pullback g).obj G) :=
      Over.OverMorphism.ext hm
    rwa [mul_eq_left] at hp
  exact (rel_iff hc hg _ _).2 (p2.trans (p1 (iota2 hg X)).symm)
end ReciprocityTheory.ChartRestriction.G.Chart

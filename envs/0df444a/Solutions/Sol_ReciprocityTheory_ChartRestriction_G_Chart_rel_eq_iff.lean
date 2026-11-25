-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.rel_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:33:38.469776+00:00
-- url     : https://prove2.me/submissions/6beaa797-c17d-4686-a78b-4c647ae64c47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_uniq_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_uniq_w


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
theorem _root_.solution {X : Over (Spec (CommRingCat.of k))} {w₁ w₂ : viaT tk X ⟶ G'} {v₁ v₂ : X ⟶ (Over.pullback g).obj G}
    (h₁ : Rel (F := F) tk g w₁ v₁) (h₂ : Rel (F := F) tk g w₂ v₂) : w₁ = w₂ ↔ v₁ = v₂ := by
  constructor
  · rintro rfl
    exact rel_uniq_v h₁ h₂
  · rintro rfl
    exact rel_uniq_w hc h₁ h₂
end ReciprocityTheory.ChartRestriction.G.Chart

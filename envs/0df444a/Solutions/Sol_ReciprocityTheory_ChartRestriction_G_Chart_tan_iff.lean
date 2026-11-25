-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tan_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:51:08.949597+00:00
-- url     : https://prove2.me/submissions/22448e43-c97a-4b4e-9360-c9c0272a1440

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_eq_iff
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_one_left__f4b8b6e904c4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_one
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
include hc hg
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    Geo.Tor.spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk tk ⟶ G').left ↔ IsTan v := by
  have h1 := rel_pre (spMap (fstD k)) h
  have h2 := rel_one hc hg (X := sp (R₀ := k) k)
  have hid : (sp (R₀ := k) k).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rfl
  have e1 : (1 : viaT tk (sp (R₀ := k) k) ⟶ G').left = (1 : Over.mk tk ⟶ G').left := by
    rw [one_left', one_left']
    show ((sp (R₀ := k) k).hom ≫ tk) ≫ _ = tk ≫ _
    rw [hid, Category.id_comp]
  rw [IsTan, ← rel_eq_iff hc h1 h2]
  constructor
  · intro e
    apply Over.OverMorphism.ext
    exact e.trans e1.symm
  · intro e
    exact (congrArg (fun q => q.left) e).trans e1
end ReciprocityTheory.ChartRestriction.G.Chart

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tanS_prodPts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:43:09.612195+00:00
-- url     : https://prove2.me/submissions/3b687b2c-c6d6-4ccf-98bf-42fd88b25d50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushRProdPtsResP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {d : ℕ} (c : Fin d → S) {u : Fin d → (sp (R₀ := S) (DualNumber S) ⟶ G)} (hu : ∀ i, TanS (u i)) :
    TanS (prodPts c u) := by
  unfold TanS prodPts
  change preH (spMap (TrivSqZeroExt.fstHom S S S)) (List.ofFn fun i => spMap (scaleD (c i)) ≫ u i).prod = 1
  rw [map_list_prod, List.map_ofFn]
  have h1 : ∀ i, preH (spMap (TrivSqZeroExt.fstHom S S S)) (spMap (scaleD (c i)) ≫ u i) = 1 :=
    fun i => tanS_scale (c i) (hu i)
  simp only [Function.comp_def, h1, List.ofFn_const, List.prod_replicate, one_pow]
end ReciprocityTheory.ChartRestriction.G.Chart

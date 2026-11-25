-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.pushR_prodPts_resP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:19:34.870214+00:00
-- url     : https://prove2.me/submissions/948e82b3-3636-4b01-b36f-6c5d8127a113

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushRProdPtsResP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_resP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dualMapS_comp_scaleS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_spMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


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
variable (p : Ideal S) [p.IsPrime]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {d : ℕ} (c : Fin d → S) (u : Fin d → (sp (R₀ := S) (DualNumber S) ⟶ G)) :
    pushR G (prodPts (fun i => algebraMap S (Localization.AtPrime p) (c i)) (fun i => resP p (u i))) =
      spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ prodPts c u := by
  unfold prodPts
  rw [pushR_prod]
  change _ = preH (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))))
    (List.ofFn fun i => spMap (scaleD (c i)) ≫ u i).prod
  rw [map_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  show pushR G (spMap (scaleD _) ≫ resP p (u i)) =
    spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ spMap (scaleD (c i)) ≫ u i
  rw [pushR_spMap, pushR_resP, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp]
  congr 2
  exact (dualMapS_comp_scaleS (Algebra.ofId S (Localization.AtPrime p)) (c i)).symm
end ReciprocityTheory.ChartRestriction.G.Chart

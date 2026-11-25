-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.scale_prodPts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:14:52.0976+00:00
-- url     : https://prove2.me/submissions/b7cf01ea-2a4f-444d-a74d-111bd16be605

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pre_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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
variable {R : Type} [CommRing R] {M : Over (Spec (CommRingCat.of R))} [GrpObj M]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {d : ℕ} (a : R) (c : Fin d → R) (v : Fin d → (sp (R₀ := R) (DualNumber R) ⟶ M)) :
    spMap (scaleD a) ≫ prodPts c v = prodPts (a • c) v := by
  unfold prodPts
  rw [pre_prod]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  have hs : (scaleD a).comp (scaleD (c i)) = scaleD ((a • c) i) := by
    apply AlgHom.ext
    intro x
    refine TrivSqZeroExt.ext ?_ ?_
    all_goals (simp only [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, AlgHom.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, Pi.smul_apply]; try ring)
  rw [← Category.assoc, spMap_comp, hs]
end ReciprocityTheory.ChartRestriction.G.Chart

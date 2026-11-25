-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateCoindIso___c9eabb086c30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:26:11.948918+00:00
-- url     : https://prove2.me/submissions/c4087da0-73ab-4789-ad2b-0cd362f60c0a

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateShapiro
import Theorems.Thm_GroundTheory_GroupCoh_homologyMap_tateShapiroMap_comp_tateCoindIso_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology groupHomology Rep HomologicalComplex
universe u
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype G] [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution {X : ShortComplex (Rep.{u} k S)} (hX : X.ShortExact) (n : ℤ) :
    TateCohomology.δ (shortExact_map_coindFunctor S hX) n ≫ (tateCoindIso S X.X₁ (n + 1)).hom =
      (tateCoindIso S X.X₃ n).hom ≫ TateCohomology.δ hX n := by
  have key := tateShapiroMap_δ S hX n
  refine (cancel_epi (HomologicalComplex.homologyMap (tateShapiroMap S X.X₃) n)).1 ?_
  refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _)
  refine (congrArg (· ≫ (tateCoindIso S X.X₁ (n + 1)).hom) key.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (TateCohomology.δ hX n ≫ ·)
    (homologyMap_tateShapiroMap_comp_tateCoindIso_hom S X.X₁ (n + 1))).trans ?_
  refine (Category.comp_id _).trans ?_
  exact ((congrArg (· ≫ TateCohomology.δ hX n)
    (homologyMap_tateShapiroMap_comp_tateCoindIso_hom S X.X₃ n)).trans (Category.id_comp _)).symm
end GroundTheory.GroupCoh

-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateIndIso___d5ad9d49d683
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:41.122824+00:00
-- url     : https://prove2.me/submissions/cf198968-32f2-47b8-95d7-fc28a32a78b1

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateShapiro
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateCoindIso___c9eabb086c30

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
    TateCohomology.δ (shortExact_map_indFunctor S hX) n ≫ (tateIndIso S X.X₁ (n + 1)).hom =
      (tateIndIso S X.X₃ n).hom ≫ TateCohomology.δ hX n := by
  classical
  have h1 := TateCohomology.δ_naturality (shortExact_map_indFunctor S hX)
    (shortExact_map_coindFunctor S hX) (X.mapNatTrans (indCoindNatIso k S).hom) n
  have h2 := tateCoindIso_δ S hX n
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (tateCoindIso S X.X₁ (n + 1)).hom) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) h2).trans ?_
  exact (Category.assoc _ _ _).symm
end GroundTheory.GroupCoh

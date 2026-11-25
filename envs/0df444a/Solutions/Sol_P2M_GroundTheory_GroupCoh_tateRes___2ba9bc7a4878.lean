-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateRes___2ba9bc7a4878
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:46.733047+00:00
-- url     : https://prove2.me/submissions/35cbc097-4a55-4bd1-bd88-f929e129b158

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateShapiro
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Theorems.Thm_GroundTheory_GroupCoh_tateRes_app
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateCoindIso___c9eabb086c30
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    TateCohomology.δ hX n ≫ (tateRes S (n + 1)).app X.X₁ =
      (tateRes S n).app X.X₃ ≫ TateCohomology.δ (shortExact_map_resFunctor S hX) n := by
  have hR := shortExact_map_resFunctor S hX
  have h1 := TateCohomology.δ_naturality hX (shortExact_map_coindFunctor S hR)
    (resCoindUnitShortComplex S X) n
  have h2 := tateCoindIso_δ S hR n
  simp only [resCoindUnitShortComplex_τ₁, resCoindUnitShortComplex_τ₃] at h1
  rw [tateRes_app, tateRes_app]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))
end GroundTheory.GroupCoh

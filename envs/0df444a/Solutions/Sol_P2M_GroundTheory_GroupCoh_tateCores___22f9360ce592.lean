-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateCores___22f9360ce592
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:55:53.638352+00:00
-- url     : https://prove2.me/submissions/cdef9de6-d8ad-46a5-b7af-491cb3f2728d

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateShapiro
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Theorems.Thm_GroundTheory_GroupCoh_tateCores_app
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateIndIso___d5ad9d49d683
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
    TateCohomology.δ (shortExact_map_resFunctor S hX) n ≫ (tateCores S (n + 1)).app X.X₁ =
      (tateCores S n).app X.X₃ ≫ TateCohomology.δ hX n := by
  have hR := shortExact_map_resFunctor S hX
  have h1 := TateCohomology.δ_naturality (shortExact_map_indFunctor S hR) hX
    (indResCounitShortComplex S X) n
  have h2 := tateIndIso_δ S hR n
  simp only [indResCounitShortComplex_τ₁, indResCounitShortComplex_τ₃] at h1
  have h3 : TateCohomology.δ hR n ≫ (tateIndIso S (X.map (resFunctor S.subtype)).X₁ (n + 1)).inv =
      (tateIndIso S (X.map (resFunctor S.subtype)).X₃ n).inv ≫
        TateCohomology.δ (shortExact_map_indFunctor S hR) n := by
    exact (Iso.inv_hom_id_assoc _ _).symm.trans (congrArg (_ ≫ ·)
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _))))))
  rw [tateCores_app, tateCores_app]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h3).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h1).trans (Category.assoc _ _ _).symm)))
end GroundTheory.GroupCoh

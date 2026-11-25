-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_d___mapRange_addEquiv_c46ee4082a24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:09:44.233833+00:00
-- url     : https://prove2.me/submissions/279b80f4-68e2-46f3-b360-544b9401bef5

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
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
open CategoryTheory Limits Rep groupHomology
universe u
variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G]
variable {A : Rep.{u} k G} {B : Rep.{u} k' G}
namespace GroundTheory.GroupCoh
theorem _root_.solution (e : A.V ≃+ B.V) (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a))
    (c : G × G →₀ A) :
    d₂₁ B (Finsupp.mapRange e (map_zero e) c) = Finsupp.mapRange e (map_zero e) (d₂₁ A c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [Finsupp.mapRange_add (map_add e), map_add, h₁, h₂]
  | single g a =>
    rw [Finsupp.mapRange_single, d₂₁_single, d₂₁_single, Finsupp.mapRange_add (map_add e),
      Finsupp.mapRange_sub (map_sub e), Finsupp.mapRange_single, Finsupp.mapRange_single,
      Finsupp.mapRange_single, he]
end GroundTheory.GroupCoh

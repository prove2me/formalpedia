-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_split__injective_819166473dcc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:49.856921+00:00
-- url     : https://prove2.me/submissions/5febdaa8-7304-4e41-b8a8-7b34da2d5edc

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
import Theorems.Thm_GroundTheory_GroupCoh_exists_eq_zsmul_augClass
import Theorems.Thm_GroundTheory_GroupCoh_card_smul_augClass
import Theorems.Thm_P2M_GroundTheory_GroupCoh_split__augClass_80c011573ab3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
variable (S : Subgroup G) [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution (h2 : addOrderOf (resClass M u S) = Nat.card S) :
    Function.Injective (splitδ M u S) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨m, rfl⟩ := exists_eq_zsmul_augClass S y
  rw [map_zsmul, splitδ_augClass] at hy
  have hd := addOrderOf_dvd_iff_zsmul_eq_zero.2 hy
  rw [h2, Nat.card_eq_fintype_card] at hd
  obtain ⟨t, rfl⟩ := hd
  rw [mul_comm, mul_zsmul, card_smul_augClass, zsmul_zero]
end GroundTheory.GroupCoh

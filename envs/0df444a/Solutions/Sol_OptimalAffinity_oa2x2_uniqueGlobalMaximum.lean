-- Prove2me | solution 1 for OptimalAffinity.oa2x2_uniqueGlobalMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:02:15.339836+00:00
-- url     : https://prove2.me/submissions/4ba18c8a-e4fc-44eb-8a74-5ad2a7b25849

module
public import Definitions.Def_proofs_OptimalAffinity_Steady
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Theorems.Thm_OptimalAffinity_oa2x2_current_le_one
public import Theorems.Thm_OptimalAffinity_oa2x2_current_eq_one_iff
public import Theorems.Thm_OptimalAffinity_oa2x2_one_one_current
public import Theorems.Thm_OptimalAffinity_oa2x2_one_one_steady


set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution : IsUniqueGlobalMaximum oa2x2 1 1 := by
  refine ⟨by norm_num, by norm_num, oa2x2_one_one_steady, ?_, ?_⟩
  · intro x y hx hy hsteady
    rw [oa2x2_one_one_current]
    exact oa2x2_current_le_one x y hy hsteady
  · intro x y hx hy hsteady heq
    rw [oa2x2_one_one_current] at heq
    exact (oa2x2_current_eq_one_iff x y hy hsteady).mp heq
end OptimalAffinity

-- Prove2me | solution 1 for OptimalAffinity.oa2x2_affinityViolation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:59:58.136659+00:00
-- url     : https://prove2.me/submissions/a5149a2f-adb6-491b-9c5f-a0edada225c1

module
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Theorems.Thm_OptimalAffinity_oa2x2_optimalAffinityExp
public import Theorems.Thm_OptimalAffinity_oa2x2_seedRatio

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution : affinityExp oa2x2 1 1 < seedRatio oa2x2 := by
  rw [oa2x2_optimalAffinityExp, oa2x2_seedRatio]
  norm_num
end OptimalAffinity

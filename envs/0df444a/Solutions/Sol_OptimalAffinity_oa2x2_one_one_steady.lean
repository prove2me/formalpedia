-- Prove2me | solution 1 for OptimalAffinity.oa2x2_one_one_steady
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:59:14.174048+00:00
-- url     : https://prove2.me/submissions/9d1bb7ea-cd0f-4b9d-b881-b4b4abacb55b

module
public import Definitions.Def_proofs_OptimalAffinity_Source
public import Definitions.Def_proofs_OptimalAffinity_Steady
public import Theorems.Thm_OptimalAffinity_oa2x2_ySteady_iff

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution : YSteady oa2x2 1 1 := by
  rw [oa2x2_ySteady_iff]
  norm_num
end OptimalAffinity

-- Prove2me | solution 1 for OptimalAffinity.oa2x2_detailedBalance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:53:33.22125+00:00
-- url     : https://prove2.me/submissions/a9b27a62-c811-4488-b8fc-f85793ccda77

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution : DetailedBalanceExists oa2x2 := by
  refine ⟨7 / 4, 21 / 8, by norm_num, by norm_num, ?_⟩
  intro r
  fin_cases r <;> norm_num [forwardFlux, reverseFlux, oa2x2]
end OptimalAffinity

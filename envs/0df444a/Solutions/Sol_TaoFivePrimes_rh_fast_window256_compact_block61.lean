-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block61
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:33:21.819392+00:00
-- url     : https://prove2.me/submissions/c3d20b80-de5f-4ffe-adac-04bddcd253c7

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock61Checks
theorem row00 : RHFastWindow256CompactReference.checked (1952+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1952+1)=true := by decide +kernel
end RHFastWindow256CompactBlock61Checks

theorem solution : RHFastWindow256CompactReference.block 1952 2=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock61Checks.row00,
  RHFastWindow256CompactBlock61Checks.row01]
#print axioms solution

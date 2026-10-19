-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block61
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:40:33.579222+00:00
-- url     : https://prove2.me/submissions/03511f8b-f818-41ce-9a7b-98d0f294255a

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block61Checks
theorem row00 : RHBatch01New256CompactReference.checked (1952+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1952+1)=true := by decide +kernel
end RHBatch01New256Block61Checks

theorem solution : RHBatch01New256CompactReference.block 1952 2=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block61Checks.row00,RHBatch01New256Block61Checks.row01]
#print axioms solution

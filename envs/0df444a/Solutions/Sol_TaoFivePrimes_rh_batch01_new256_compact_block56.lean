-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block56
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:36:49.167018+00:00
-- url     : https://prove2.me/submissions/a7ceb0c2-3488-463d-bc76-1bed8b9a1dcd

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block56Checks
theorem row00 : RHBatch01New256CompactReference.checked (1792+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1792+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1792+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1792+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1792+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1792+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1792+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1792+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1792+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1792+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1792+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1792+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1792+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1792+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1792+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1792+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1792+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1792+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1792+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1792+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1792+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1792+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1792+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1792+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1792+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1792+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1792+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1792+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1792+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1792+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1792+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1792+31)=true := by decide +kernel
end RHBatch01New256Block56Checks

theorem solution : RHBatch01New256CompactReference.block 1792 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block56Checks.row00,RHBatch01New256Block56Checks.row01,RHBatch01New256Block56Checks.row02,RHBatch01New256Block56Checks.row03,RHBatch01New256Block56Checks.row04,RHBatch01New256Block56Checks.row05,RHBatch01New256Block56Checks.row06,RHBatch01New256Block56Checks.row07,RHBatch01New256Block56Checks.row08,RHBatch01New256Block56Checks.row09,RHBatch01New256Block56Checks.row10,RHBatch01New256Block56Checks.row11,RHBatch01New256Block56Checks.row12,RHBatch01New256Block56Checks.row13,RHBatch01New256Block56Checks.row14,RHBatch01New256Block56Checks.row15,RHBatch01New256Block56Checks.row16,RHBatch01New256Block56Checks.row17,RHBatch01New256Block56Checks.row18,RHBatch01New256Block56Checks.row19,RHBatch01New256Block56Checks.row20,RHBatch01New256Block56Checks.row21,RHBatch01New256Block56Checks.row22,RHBatch01New256Block56Checks.row23,RHBatch01New256Block56Checks.row24,RHBatch01New256Block56Checks.row25,RHBatch01New256Block56Checks.row26,RHBatch01New256Block56Checks.row27,RHBatch01New256Block56Checks.row28,RHBatch01New256Block56Checks.row29,RHBatch01New256Block56Checks.row30,RHBatch01New256Block56Checks.row31]
#print axioms solution

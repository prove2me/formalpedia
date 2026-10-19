-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block12
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:59:38.054193+00:00
-- url     : https://prove2.me/submissions/70425b9b-b422-463c-ae97-5513d50de30f

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block12Checks
theorem row00 : RHBatch01New256CompactReference.checked (384+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (384+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (384+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (384+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (384+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (384+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (384+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (384+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (384+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (384+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (384+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (384+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (384+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (384+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (384+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (384+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (384+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (384+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (384+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (384+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (384+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (384+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (384+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (384+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (384+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (384+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (384+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (384+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (384+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (384+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (384+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (384+31)=true := by decide +kernel
end RHBatch01New256Block12Checks

theorem solution : RHBatch01New256CompactReference.block 384 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block12Checks.row00,RHBatch01New256Block12Checks.row01,RHBatch01New256Block12Checks.row02,RHBatch01New256Block12Checks.row03,RHBatch01New256Block12Checks.row04,RHBatch01New256Block12Checks.row05,RHBatch01New256Block12Checks.row06,RHBatch01New256Block12Checks.row07,RHBatch01New256Block12Checks.row08,RHBatch01New256Block12Checks.row09,RHBatch01New256Block12Checks.row10,RHBatch01New256Block12Checks.row11,RHBatch01New256Block12Checks.row12,RHBatch01New256Block12Checks.row13,RHBatch01New256Block12Checks.row14,RHBatch01New256Block12Checks.row15,RHBatch01New256Block12Checks.row16,RHBatch01New256Block12Checks.row17,RHBatch01New256Block12Checks.row18,RHBatch01New256Block12Checks.row19,RHBatch01New256Block12Checks.row20,RHBatch01New256Block12Checks.row21,RHBatch01New256Block12Checks.row22,RHBatch01New256Block12Checks.row23,RHBatch01New256Block12Checks.row24,RHBatch01New256Block12Checks.row25,RHBatch01New256Block12Checks.row26,RHBatch01New256Block12Checks.row27,RHBatch01New256Block12Checks.row28,RHBatch01New256Block12Checks.row29,RHBatch01New256Block12Checks.row30,RHBatch01New256Block12Checks.row31]
#print axioms solution

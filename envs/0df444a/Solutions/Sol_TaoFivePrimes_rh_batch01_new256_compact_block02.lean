-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block02
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:30:22.523713+00:00
-- url     : https://prove2.me/submissions/c5486c69-6fda-42a4-8c3a-ae1657583622

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block02Checks
theorem row00 : RHBatch01New256CompactReference.checked (64+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (64+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (64+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (64+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (64+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (64+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (64+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (64+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (64+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (64+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (64+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (64+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (64+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (64+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (64+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (64+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (64+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (64+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (64+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (64+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (64+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (64+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (64+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (64+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (64+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (64+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (64+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (64+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (64+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (64+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (64+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (64+31)=true := by decide +kernel
end RHBatch01New256Block02Checks

theorem solution : RHBatch01New256CompactReference.block 64 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block02Checks.row00,RHBatch01New256Block02Checks.row01,RHBatch01New256Block02Checks.row02,RHBatch01New256Block02Checks.row03,RHBatch01New256Block02Checks.row04,RHBatch01New256Block02Checks.row05,RHBatch01New256Block02Checks.row06,RHBatch01New256Block02Checks.row07,RHBatch01New256Block02Checks.row08,RHBatch01New256Block02Checks.row09,RHBatch01New256Block02Checks.row10,RHBatch01New256Block02Checks.row11,RHBatch01New256Block02Checks.row12,RHBatch01New256Block02Checks.row13,RHBatch01New256Block02Checks.row14,RHBatch01New256Block02Checks.row15,RHBatch01New256Block02Checks.row16,RHBatch01New256Block02Checks.row17,RHBatch01New256Block02Checks.row18,RHBatch01New256Block02Checks.row19,RHBatch01New256Block02Checks.row20,RHBatch01New256Block02Checks.row21,RHBatch01New256Block02Checks.row22,RHBatch01New256Block02Checks.row23,RHBatch01New256Block02Checks.row24,RHBatch01New256Block02Checks.row25,RHBatch01New256Block02Checks.row26,RHBatch01New256Block02Checks.row27,RHBatch01New256Block02Checks.row28,RHBatch01New256Block02Checks.row29,RHBatch01New256Block02Checks.row30,RHBatch01New256Block02Checks.row31]
#print axioms solution

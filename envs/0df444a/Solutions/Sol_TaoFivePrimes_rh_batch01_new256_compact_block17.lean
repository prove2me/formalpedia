-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block17
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T14:35:25.467176+00:00
-- url     : https://prove2.me/submissions/19508c69-ad98-43f7-8273-52f7a206f2bd

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block17Checks
theorem row00 : RHBatch01New256CompactReference.checked (544+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (544+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (544+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (544+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (544+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (544+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (544+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (544+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (544+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (544+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (544+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (544+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (544+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (544+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (544+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (544+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (544+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (544+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (544+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (544+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (544+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (544+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (544+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (544+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (544+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (544+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (544+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (544+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (544+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (544+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (544+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (544+31)=true := by decide +kernel
end RHBatch01New256Block17Checks

theorem solution : RHBatch01New256CompactReference.block 544 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block17Checks.row00,RHBatch01New256Block17Checks.row01,RHBatch01New256Block17Checks.row02,RHBatch01New256Block17Checks.row03,RHBatch01New256Block17Checks.row04,RHBatch01New256Block17Checks.row05,RHBatch01New256Block17Checks.row06,RHBatch01New256Block17Checks.row07,RHBatch01New256Block17Checks.row08,RHBatch01New256Block17Checks.row09,RHBatch01New256Block17Checks.row10,RHBatch01New256Block17Checks.row11,RHBatch01New256Block17Checks.row12,RHBatch01New256Block17Checks.row13,RHBatch01New256Block17Checks.row14,RHBatch01New256Block17Checks.row15,RHBatch01New256Block17Checks.row16,RHBatch01New256Block17Checks.row17,RHBatch01New256Block17Checks.row18,RHBatch01New256Block17Checks.row19,RHBatch01New256Block17Checks.row20,RHBatch01New256Block17Checks.row21,RHBatch01New256Block17Checks.row22,RHBatch01New256Block17Checks.row23,RHBatch01New256Block17Checks.row24,RHBatch01New256Block17Checks.row25,RHBatch01New256Block17Checks.row26,RHBatch01New256Block17Checks.row27,RHBatch01New256Block17Checks.row28,RHBatch01New256Block17Checks.row29,RHBatch01New256Block17Checks.row30,RHBatch01New256Block17Checks.row31]
#print axioms solution

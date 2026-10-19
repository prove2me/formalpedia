-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block13
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T14:09:52.522256+00:00
-- url     : https://prove2.me/submissions/c4b01c89-ee77-4e4f-a083-5b911bd7a4a1

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block13Checks
theorem row00 : RHBatch01New256CompactReference.checked (416+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (416+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (416+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (416+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (416+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (416+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (416+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (416+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (416+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (416+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (416+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (416+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (416+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (416+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (416+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (416+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (416+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (416+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (416+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (416+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (416+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (416+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (416+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (416+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (416+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (416+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (416+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (416+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (416+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (416+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (416+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (416+31)=true := by decide +kernel
end RHBatch01New256Block13Checks

theorem solution : RHBatch01New256CompactReference.block 416 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block13Checks.row00,RHBatch01New256Block13Checks.row01,RHBatch01New256Block13Checks.row02,RHBatch01New256Block13Checks.row03,RHBatch01New256Block13Checks.row04,RHBatch01New256Block13Checks.row05,RHBatch01New256Block13Checks.row06,RHBatch01New256Block13Checks.row07,RHBatch01New256Block13Checks.row08,RHBatch01New256Block13Checks.row09,RHBatch01New256Block13Checks.row10,RHBatch01New256Block13Checks.row11,RHBatch01New256Block13Checks.row12,RHBatch01New256Block13Checks.row13,RHBatch01New256Block13Checks.row14,RHBatch01New256Block13Checks.row15,RHBatch01New256Block13Checks.row16,RHBatch01New256Block13Checks.row17,RHBatch01New256Block13Checks.row18,RHBatch01New256Block13Checks.row19,RHBatch01New256Block13Checks.row20,RHBatch01New256Block13Checks.row21,RHBatch01New256Block13Checks.row22,RHBatch01New256Block13Checks.row23,RHBatch01New256Block13Checks.row24,RHBatch01New256Block13Checks.row25,RHBatch01New256Block13Checks.row26,RHBatch01New256Block13Checks.row27,RHBatch01New256Block13Checks.row28,RHBatch01New256Block13Checks.row29,RHBatch01New256Block13Checks.row30,RHBatch01New256Block13Checks.row31]
#print axioms solution

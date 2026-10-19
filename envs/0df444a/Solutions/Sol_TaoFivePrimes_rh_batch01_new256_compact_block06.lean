-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block06
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:38:46.731513+00:00
-- url     : https://prove2.me/submissions/2069430d-fad4-4352-85d7-f781bf4f5dad

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block06Checks
theorem row00 : RHBatch01New256CompactReference.checked (192+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (192+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (192+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (192+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (192+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (192+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (192+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (192+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (192+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (192+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (192+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (192+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (192+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (192+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (192+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (192+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (192+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (192+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (192+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (192+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (192+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (192+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (192+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (192+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (192+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (192+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (192+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (192+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (192+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (192+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (192+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (192+31)=true := by decide +kernel
end RHBatch01New256Block06Checks

theorem solution : RHBatch01New256CompactReference.block 192 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block06Checks.row00,RHBatch01New256Block06Checks.row01,RHBatch01New256Block06Checks.row02,RHBatch01New256Block06Checks.row03,RHBatch01New256Block06Checks.row04,RHBatch01New256Block06Checks.row05,RHBatch01New256Block06Checks.row06,RHBatch01New256Block06Checks.row07,RHBatch01New256Block06Checks.row08,RHBatch01New256Block06Checks.row09,RHBatch01New256Block06Checks.row10,RHBatch01New256Block06Checks.row11,RHBatch01New256Block06Checks.row12,RHBatch01New256Block06Checks.row13,RHBatch01New256Block06Checks.row14,RHBatch01New256Block06Checks.row15,RHBatch01New256Block06Checks.row16,RHBatch01New256Block06Checks.row17,RHBatch01New256Block06Checks.row18,RHBatch01New256Block06Checks.row19,RHBatch01New256Block06Checks.row20,RHBatch01New256Block06Checks.row21,RHBatch01New256Block06Checks.row22,RHBatch01New256Block06Checks.row23,RHBatch01New256Block06Checks.row24,RHBatch01New256Block06Checks.row25,RHBatch01New256Block06Checks.row26,RHBatch01New256Block06Checks.row27,RHBatch01New256Block06Checks.row28,RHBatch01New256Block06Checks.row29,RHBatch01New256Block06Checks.row30,RHBatch01New256Block06Checks.row31]
#print axioms solution

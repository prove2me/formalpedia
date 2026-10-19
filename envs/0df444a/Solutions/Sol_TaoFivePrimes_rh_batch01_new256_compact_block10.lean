-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block10
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:49:53.544071+00:00
-- url     : https://prove2.me/submissions/216afed2-674f-48f7-bde8-0642f206a07e

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block10Checks
theorem row00 : RHBatch01New256CompactReference.checked (320+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (320+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (320+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (320+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (320+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (320+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (320+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (320+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (320+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (320+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (320+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (320+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (320+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (320+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (320+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (320+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (320+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (320+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (320+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (320+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (320+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (320+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (320+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (320+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (320+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (320+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (320+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (320+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (320+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (320+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (320+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (320+31)=true := by decide +kernel
end RHBatch01New256Block10Checks

theorem solution : RHBatch01New256CompactReference.block 320 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block10Checks.row00,RHBatch01New256Block10Checks.row01,RHBatch01New256Block10Checks.row02,RHBatch01New256Block10Checks.row03,RHBatch01New256Block10Checks.row04,RHBatch01New256Block10Checks.row05,RHBatch01New256Block10Checks.row06,RHBatch01New256Block10Checks.row07,RHBatch01New256Block10Checks.row08,RHBatch01New256Block10Checks.row09,RHBatch01New256Block10Checks.row10,RHBatch01New256Block10Checks.row11,RHBatch01New256Block10Checks.row12,RHBatch01New256Block10Checks.row13,RHBatch01New256Block10Checks.row14,RHBatch01New256Block10Checks.row15,RHBatch01New256Block10Checks.row16,RHBatch01New256Block10Checks.row17,RHBatch01New256Block10Checks.row18,RHBatch01New256Block10Checks.row19,RHBatch01New256Block10Checks.row20,RHBatch01New256Block10Checks.row21,RHBatch01New256Block10Checks.row22,RHBatch01New256Block10Checks.row23,RHBatch01New256Block10Checks.row24,RHBatch01New256Block10Checks.row25,RHBatch01New256Block10Checks.row26,RHBatch01New256Block10Checks.row27,RHBatch01New256Block10Checks.row28,RHBatch01New256Block10Checks.row29,RHBatch01New256Block10Checks.row30,RHBatch01New256Block10Checks.row31]
#print axioms solution

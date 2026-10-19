-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block43
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:21:18.626157+00:00
-- url     : https://prove2.me/submissions/341f0b5b-6e19-44e5-aef1-6fcb9301d890

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block43Checks
theorem row00 : RHBatch01New256CompactReference.checked (1376+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1376+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1376+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1376+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1376+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1376+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1376+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1376+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1376+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1376+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1376+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1376+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1376+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1376+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1376+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1376+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1376+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1376+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1376+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1376+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1376+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1376+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1376+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1376+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1376+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1376+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1376+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1376+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1376+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1376+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1376+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1376+31)=true := by decide +kernel
end RHBatch01New256Block43Checks

theorem solution : RHBatch01New256CompactReference.block 1376 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block43Checks.row00,RHBatch01New256Block43Checks.row01,RHBatch01New256Block43Checks.row02,RHBatch01New256Block43Checks.row03,RHBatch01New256Block43Checks.row04,RHBatch01New256Block43Checks.row05,RHBatch01New256Block43Checks.row06,RHBatch01New256Block43Checks.row07,RHBatch01New256Block43Checks.row08,RHBatch01New256Block43Checks.row09,RHBatch01New256Block43Checks.row10,RHBatch01New256Block43Checks.row11,RHBatch01New256Block43Checks.row12,RHBatch01New256Block43Checks.row13,RHBatch01New256Block43Checks.row14,RHBatch01New256Block43Checks.row15,RHBatch01New256Block43Checks.row16,RHBatch01New256Block43Checks.row17,RHBatch01New256Block43Checks.row18,RHBatch01New256Block43Checks.row19,RHBatch01New256Block43Checks.row20,RHBatch01New256Block43Checks.row21,RHBatch01New256Block43Checks.row22,RHBatch01New256Block43Checks.row23,RHBatch01New256Block43Checks.row24,RHBatch01New256Block43Checks.row25,RHBatch01New256Block43Checks.row26,RHBatch01New256Block43Checks.row27,RHBatch01New256Block43Checks.row28,RHBatch01New256Block43Checks.row29,RHBatch01New256Block43Checks.row30,RHBatch01New256Block43Checks.row31]
#print axioms solution

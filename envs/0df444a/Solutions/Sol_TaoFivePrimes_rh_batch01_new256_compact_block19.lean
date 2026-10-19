-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block19
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T14:44:34.151884+00:00
-- url     : https://prove2.me/submissions/afd0cbdf-55f8-499d-9bf1-cc7a71200fbf

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block19Checks
theorem row00 : RHBatch01New256CompactReference.checked (608+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (608+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (608+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (608+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (608+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (608+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (608+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (608+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (608+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (608+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (608+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (608+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (608+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (608+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (608+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (608+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (608+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (608+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (608+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (608+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (608+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (608+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (608+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (608+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (608+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (608+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (608+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (608+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (608+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (608+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (608+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (608+31)=true := by decide +kernel
end RHBatch01New256Block19Checks

theorem solution : RHBatch01New256CompactReference.block 608 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block19Checks.row00,RHBatch01New256Block19Checks.row01,RHBatch01New256Block19Checks.row02,RHBatch01New256Block19Checks.row03,RHBatch01New256Block19Checks.row04,RHBatch01New256Block19Checks.row05,RHBatch01New256Block19Checks.row06,RHBatch01New256Block19Checks.row07,RHBatch01New256Block19Checks.row08,RHBatch01New256Block19Checks.row09,RHBatch01New256Block19Checks.row10,RHBatch01New256Block19Checks.row11,RHBatch01New256Block19Checks.row12,RHBatch01New256Block19Checks.row13,RHBatch01New256Block19Checks.row14,RHBatch01New256Block19Checks.row15,RHBatch01New256Block19Checks.row16,RHBatch01New256Block19Checks.row17,RHBatch01New256Block19Checks.row18,RHBatch01New256Block19Checks.row19,RHBatch01New256Block19Checks.row20,RHBatch01New256Block19Checks.row21,RHBatch01New256Block19Checks.row22,RHBatch01New256Block19Checks.row23,RHBatch01New256Block19Checks.row24,RHBatch01New256Block19Checks.row25,RHBatch01New256Block19Checks.row26,RHBatch01New256Block19Checks.row27,RHBatch01New256Block19Checks.row28,RHBatch01New256Block19Checks.row29,RHBatch01New256Block19Checks.row30,RHBatch01New256Block19Checks.row31]
#print axioms solution

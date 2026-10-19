-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block32
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:01:54.183334+00:00
-- url     : https://prove2.me/submissions/4e72cc88-440d-4838-aba9-f3a2a36004da

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block32Checks
theorem row00 : RHBatch01New256CompactReference.checked (1024+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1024+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1024+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1024+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1024+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1024+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1024+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1024+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1024+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1024+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1024+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1024+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1024+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1024+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1024+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1024+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1024+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1024+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1024+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1024+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1024+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1024+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1024+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1024+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1024+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1024+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1024+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1024+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1024+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1024+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1024+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1024+31)=true := by decide +kernel
end RHBatch01New256Block32Checks

theorem solution : RHBatch01New256CompactReference.block 1024 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block32Checks.row00,RHBatch01New256Block32Checks.row01,RHBatch01New256Block32Checks.row02,RHBatch01New256Block32Checks.row03,RHBatch01New256Block32Checks.row04,RHBatch01New256Block32Checks.row05,RHBatch01New256Block32Checks.row06,RHBatch01New256Block32Checks.row07,RHBatch01New256Block32Checks.row08,RHBatch01New256Block32Checks.row09,RHBatch01New256Block32Checks.row10,RHBatch01New256Block32Checks.row11,RHBatch01New256Block32Checks.row12,RHBatch01New256Block32Checks.row13,RHBatch01New256Block32Checks.row14,RHBatch01New256Block32Checks.row15,RHBatch01New256Block32Checks.row16,RHBatch01New256Block32Checks.row17,RHBatch01New256Block32Checks.row18,RHBatch01New256Block32Checks.row19,RHBatch01New256Block32Checks.row20,RHBatch01New256Block32Checks.row21,RHBatch01New256Block32Checks.row22,RHBatch01New256Block32Checks.row23,RHBatch01New256Block32Checks.row24,RHBatch01New256Block32Checks.row25,RHBatch01New256Block32Checks.row26,RHBatch01New256Block32Checks.row27,RHBatch01New256Block32Checks.row28,RHBatch01New256Block32Checks.row29,RHBatch01New256Block32Checks.row30,RHBatch01New256Block32Checks.row31]
#print axioms solution

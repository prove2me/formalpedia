-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block15
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T14:29:42.676184+00:00
-- url     : https://prove2.me/submissions/316a62fa-62e3-4b99-9f0f-0d0333530fdc

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block15Checks
theorem row00 : RHBatch01New256CompactReference.checked (480+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (480+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (480+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (480+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (480+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (480+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (480+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (480+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (480+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (480+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (480+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (480+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (480+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (480+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (480+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (480+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (480+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (480+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (480+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (480+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (480+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (480+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (480+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (480+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (480+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (480+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (480+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (480+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (480+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (480+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (480+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (480+31)=true := by decide +kernel
end RHBatch01New256Block15Checks

theorem solution : RHBatch01New256CompactReference.block 480 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block15Checks.row00,RHBatch01New256Block15Checks.row01,RHBatch01New256Block15Checks.row02,RHBatch01New256Block15Checks.row03,RHBatch01New256Block15Checks.row04,RHBatch01New256Block15Checks.row05,RHBatch01New256Block15Checks.row06,RHBatch01New256Block15Checks.row07,RHBatch01New256Block15Checks.row08,RHBatch01New256Block15Checks.row09,RHBatch01New256Block15Checks.row10,RHBatch01New256Block15Checks.row11,RHBatch01New256Block15Checks.row12,RHBatch01New256Block15Checks.row13,RHBatch01New256Block15Checks.row14,RHBatch01New256Block15Checks.row15,RHBatch01New256Block15Checks.row16,RHBatch01New256Block15Checks.row17,RHBatch01New256Block15Checks.row18,RHBatch01New256Block15Checks.row19,RHBatch01New256Block15Checks.row20,RHBatch01New256Block15Checks.row21,RHBatch01New256Block15Checks.row22,RHBatch01New256Block15Checks.row23,RHBatch01New256Block15Checks.row24,RHBatch01New256Block15Checks.row25,RHBatch01New256Block15Checks.row26,RHBatch01New256Block15Checks.row27,RHBatch01New256Block15Checks.row28,RHBatch01New256Block15Checks.row29,RHBatch01New256Block15Checks.row30,RHBatch01New256Block15Checks.row31]
#print axioms solution

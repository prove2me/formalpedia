-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block20
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T14:46:19.237095+00:00
-- url     : https://prove2.me/submissions/1d3bdf27-8578-4eb2-8655-cf143ec6c487

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block20Checks
theorem row00 : RHBatch01New256CompactReference.checked (640+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (640+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (640+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (640+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (640+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (640+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (640+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (640+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (640+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (640+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (640+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (640+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (640+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (640+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (640+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (640+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (640+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (640+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (640+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (640+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (640+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (640+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (640+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (640+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (640+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (640+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (640+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (640+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (640+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (640+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (640+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (640+31)=true := by decide +kernel
end RHBatch01New256Block20Checks

theorem solution : RHBatch01New256CompactReference.block 640 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block20Checks.row00,RHBatch01New256Block20Checks.row01,RHBatch01New256Block20Checks.row02,RHBatch01New256Block20Checks.row03,RHBatch01New256Block20Checks.row04,RHBatch01New256Block20Checks.row05,RHBatch01New256Block20Checks.row06,RHBatch01New256Block20Checks.row07,RHBatch01New256Block20Checks.row08,RHBatch01New256Block20Checks.row09,RHBatch01New256Block20Checks.row10,RHBatch01New256Block20Checks.row11,RHBatch01New256Block20Checks.row12,RHBatch01New256Block20Checks.row13,RHBatch01New256Block20Checks.row14,RHBatch01New256Block20Checks.row15,RHBatch01New256Block20Checks.row16,RHBatch01New256Block20Checks.row17,RHBatch01New256Block20Checks.row18,RHBatch01New256Block20Checks.row19,RHBatch01New256Block20Checks.row20,RHBatch01New256Block20Checks.row21,RHBatch01New256Block20Checks.row22,RHBatch01New256Block20Checks.row23,RHBatch01New256Block20Checks.row24,RHBatch01New256Block20Checks.row25,RHBatch01New256Block20Checks.row26,RHBatch01New256Block20Checks.row27,RHBatch01New256Block20Checks.row28,RHBatch01New256Block20Checks.row29,RHBatch01New256Block20Checks.row30,RHBatch01New256Block20Checks.row31]
#print axioms solution

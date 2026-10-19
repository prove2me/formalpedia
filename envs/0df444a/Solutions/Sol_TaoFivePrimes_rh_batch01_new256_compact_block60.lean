-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block60
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:39:36.271118+00:00
-- url     : https://prove2.me/submissions/301e1637-516a-40a4-8ba9-4b64a92bc577

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block60Checks
theorem row00 : RHBatch01New256CompactReference.checked (1920+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1920+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1920+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1920+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1920+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1920+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1920+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1920+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1920+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1920+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1920+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1920+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1920+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1920+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1920+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1920+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1920+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1920+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1920+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1920+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1920+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1920+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1920+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1920+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1920+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1920+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1920+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1920+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1920+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1920+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1920+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1920+31)=true := by decide +kernel
end RHBatch01New256Block60Checks

theorem solution : RHBatch01New256CompactReference.block 1920 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block60Checks.row00,RHBatch01New256Block60Checks.row01,RHBatch01New256Block60Checks.row02,RHBatch01New256Block60Checks.row03,RHBatch01New256Block60Checks.row04,RHBatch01New256Block60Checks.row05,RHBatch01New256Block60Checks.row06,RHBatch01New256Block60Checks.row07,RHBatch01New256Block60Checks.row08,RHBatch01New256Block60Checks.row09,RHBatch01New256Block60Checks.row10,RHBatch01New256Block60Checks.row11,RHBatch01New256Block60Checks.row12,RHBatch01New256Block60Checks.row13,RHBatch01New256Block60Checks.row14,RHBatch01New256Block60Checks.row15,RHBatch01New256Block60Checks.row16,RHBatch01New256Block60Checks.row17,RHBatch01New256Block60Checks.row18,RHBatch01New256Block60Checks.row19,RHBatch01New256Block60Checks.row20,RHBatch01New256Block60Checks.row21,RHBatch01New256Block60Checks.row22,RHBatch01New256Block60Checks.row23,RHBatch01New256Block60Checks.row24,RHBatch01New256Block60Checks.row25,RHBatch01New256Block60Checks.row26,RHBatch01New256Block60Checks.row27,RHBatch01New256Block60Checks.row28,RHBatch01New256Block60Checks.row29,RHBatch01New256Block60Checks.row30,RHBatch01New256Block60Checks.row31]
#print axioms solution

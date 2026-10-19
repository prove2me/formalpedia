-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block57
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:37:45.01217+00:00
-- url     : https://prove2.me/submissions/e8b8c1bc-aa24-4ec4-8189-892ae4ab44d6

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block57Checks
theorem row00 : RHBatch01New256CompactReference.checked (1824+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1824+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1824+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1824+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1824+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1824+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1824+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1824+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1824+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1824+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1824+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1824+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1824+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1824+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1824+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1824+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1824+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1824+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1824+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1824+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1824+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1824+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1824+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1824+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1824+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1824+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1824+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1824+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1824+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1824+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1824+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1824+31)=true := by decide +kernel
end RHBatch01New256Block57Checks

theorem solution : RHBatch01New256CompactReference.block 1824 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block57Checks.row00,RHBatch01New256Block57Checks.row01,RHBatch01New256Block57Checks.row02,RHBatch01New256Block57Checks.row03,RHBatch01New256Block57Checks.row04,RHBatch01New256Block57Checks.row05,RHBatch01New256Block57Checks.row06,RHBatch01New256Block57Checks.row07,RHBatch01New256Block57Checks.row08,RHBatch01New256Block57Checks.row09,RHBatch01New256Block57Checks.row10,RHBatch01New256Block57Checks.row11,RHBatch01New256Block57Checks.row12,RHBatch01New256Block57Checks.row13,RHBatch01New256Block57Checks.row14,RHBatch01New256Block57Checks.row15,RHBatch01New256Block57Checks.row16,RHBatch01New256Block57Checks.row17,RHBatch01New256Block57Checks.row18,RHBatch01New256Block57Checks.row19,RHBatch01New256Block57Checks.row20,RHBatch01New256Block57Checks.row21,RHBatch01New256Block57Checks.row22,RHBatch01New256Block57Checks.row23,RHBatch01New256Block57Checks.row24,RHBatch01New256Block57Checks.row25,RHBatch01New256Block57Checks.row26,RHBatch01New256Block57Checks.row27,RHBatch01New256Block57Checks.row28,RHBatch01New256Block57Checks.row29,RHBatch01New256Block57Checks.row30,RHBatch01New256Block57Checks.row31]
#print axioms solution

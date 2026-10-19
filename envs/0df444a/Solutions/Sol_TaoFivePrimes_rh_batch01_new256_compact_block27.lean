-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block27
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T15:42:28.660787+00:00
-- url     : https://prove2.me/submissions/2d4a3e7c-bf46-4fda-a3af-b21c82bb844d

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block27Checks
theorem row00 : RHBatch01New256CompactReference.checked (864+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (864+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (864+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (864+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (864+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (864+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (864+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (864+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (864+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (864+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (864+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (864+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (864+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (864+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (864+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (864+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (864+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (864+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (864+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (864+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (864+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (864+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (864+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (864+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (864+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (864+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (864+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (864+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (864+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (864+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (864+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (864+31)=true := by decide +kernel
end RHBatch01New256Block27Checks

theorem solution : RHBatch01New256CompactReference.block 864 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block27Checks.row00,RHBatch01New256Block27Checks.row01,RHBatch01New256Block27Checks.row02,RHBatch01New256Block27Checks.row03,RHBatch01New256Block27Checks.row04,RHBatch01New256Block27Checks.row05,RHBatch01New256Block27Checks.row06,RHBatch01New256Block27Checks.row07,RHBatch01New256Block27Checks.row08,RHBatch01New256Block27Checks.row09,RHBatch01New256Block27Checks.row10,RHBatch01New256Block27Checks.row11,RHBatch01New256Block27Checks.row12,RHBatch01New256Block27Checks.row13,RHBatch01New256Block27Checks.row14,RHBatch01New256Block27Checks.row15,RHBatch01New256Block27Checks.row16,RHBatch01New256Block27Checks.row17,RHBatch01New256Block27Checks.row18,RHBatch01New256Block27Checks.row19,RHBatch01New256Block27Checks.row20,RHBatch01New256Block27Checks.row21,RHBatch01New256Block27Checks.row22,RHBatch01New256Block27Checks.row23,RHBatch01New256Block27Checks.row24,RHBatch01New256Block27Checks.row25,RHBatch01New256Block27Checks.row26,RHBatch01New256Block27Checks.row27,RHBatch01New256Block27Checks.row28,RHBatch01New256Block27Checks.row29,RHBatch01New256Block27Checks.row30,RHBatch01New256Block27Checks.row31]
#print axioms solution

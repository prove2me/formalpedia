-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block45
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:23:08.779982+00:00
-- url     : https://prove2.me/submissions/6c6f4071-a685-41f3-a4a6-59fb071346c7

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block45Checks
theorem row00 : RHBatch01New256CompactReference.checked (1440+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1440+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1440+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1440+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1440+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1440+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1440+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1440+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1440+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1440+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1440+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1440+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1440+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1440+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1440+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1440+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1440+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1440+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1440+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1440+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1440+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1440+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1440+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1440+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1440+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1440+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1440+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1440+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1440+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1440+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1440+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1440+31)=true := by decide +kernel
end RHBatch01New256Block45Checks

theorem solution : RHBatch01New256CompactReference.block 1440 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block45Checks.row00,RHBatch01New256Block45Checks.row01,RHBatch01New256Block45Checks.row02,RHBatch01New256Block45Checks.row03,RHBatch01New256Block45Checks.row04,RHBatch01New256Block45Checks.row05,RHBatch01New256Block45Checks.row06,RHBatch01New256Block45Checks.row07,RHBatch01New256Block45Checks.row08,RHBatch01New256Block45Checks.row09,RHBatch01New256Block45Checks.row10,RHBatch01New256Block45Checks.row11,RHBatch01New256Block45Checks.row12,RHBatch01New256Block45Checks.row13,RHBatch01New256Block45Checks.row14,RHBatch01New256Block45Checks.row15,RHBatch01New256Block45Checks.row16,RHBatch01New256Block45Checks.row17,RHBatch01New256Block45Checks.row18,RHBatch01New256Block45Checks.row19,RHBatch01New256Block45Checks.row20,RHBatch01New256Block45Checks.row21,RHBatch01New256Block45Checks.row22,RHBatch01New256Block45Checks.row23,RHBatch01New256Block45Checks.row24,RHBatch01New256Block45Checks.row25,RHBatch01New256Block45Checks.row26,RHBatch01New256Block45Checks.row27,RHBatch01New256Block45Checks.row28,RHBatch01New256Block45Checks.row29,RHBatch01New256Block45Checks.row30,RHBatch01New256Block45Checks.row31]
#print axioms solution

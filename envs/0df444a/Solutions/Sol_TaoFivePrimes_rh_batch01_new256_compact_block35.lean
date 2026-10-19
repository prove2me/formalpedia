-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block35
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:10:25.739347+00:00
-- url     : https://prove2.me/submissions/343e6cba-7395-4143-9f77-60173564c3dc

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block35Checks
theorem row00 : RHBatch01New256CompactReference.checked (1120+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1120+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1120+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1120+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1120+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1120+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1120+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1120+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1120+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1120+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1120+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1120+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1120+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1120+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1120+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1120+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1120+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1120+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1120+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1120+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1120+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1120+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1120+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1120+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1120+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1120+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1120+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1120+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1120+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1120+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1120+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1120+31)=true := by decide +kernel
end RHBatch01New256Block35Checks

theorem solution : RHBatch01New256CompactReference.block 1120 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block35Checks.row00,RHBatch01New256Block35Checks.row01,RHBatch01New256Block35Checks.row02,RHBatch01New256Block35Checks.row03,RHBatch01New256Block35Checks.row04,RHBatch01New256Block35Checks.row05,RHBatch01New256Block35Checks.row06,RHBatch01New256Block35Checks.row07,RHBatch01New256Block35Checks.row08,RHBatch01New256Block35Checks.row09,RHBatch01New256Block35Checks.row10,RHBatch01New256Block35Checks.row11,RHBatch01New256Block35Checks.row12,RHBatch01New256Block35Checks.row13,RHBatch01New256Block35Checks.row14,RHBatch01New256Block35Checks.row15,RHBatch01New256Block35Checks.row16,RHBatch01New256Block35Checks.row17,RHBatch01New256Block35Checks.row18,RHBatch01New256Block35Checks.row19,RHBatch01New256Block35Checks.row20,RHBatch01New256Block35Checks.row21,RHBatch01New256Block35Checks.row22,RHBatch01New256Block35Checks.row23,RHBatch01New256Block35Checks.row24,RHBatch01New256Block35Checks.row25,RHBatch01New256Block35Checks.row26,RHBatch01New256Block35Checks.row27,RHBatch01New256Block35Checks.row28,RHBatch01New256Block35Checks.row29,RHBatch01New256Block35Checks.row30,RHBatch01New256Block35Checks.row31]
#print axioms solution

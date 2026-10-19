-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block39
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:17:37.721981+00:00
-- url     : https://prove2.me/submissions/39474723-3511-413d-be77-14ec376b01ec

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block39Checks
theorem row00 : RHBatch01New256CompactReference.checked (1248+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1248+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1248+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1248+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1248+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1248+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1248+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1248+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1248+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1248+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1248+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1248+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1248+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1248+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1248+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1248+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1248+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1248+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1248+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1248+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1248+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1248+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1248+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1248+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1248+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1248+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1248+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1248+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1248+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1248+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1248+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1248+31)=true := by decide +kernel
end RHBatch01New256Block39Checks

theorem solution : RHBatch01New256CompactReference.block 1248 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block39Checks.row00,RHBatch01New256Block39Checks.row01,RHBatch01New256Block39Checks.row02,RHBatch01New256Block39Checks.row03,RHBatch01New256Block39Checks.row04,RHBatch01New256Block39Checks.row05,RHBatch01New256Block39Checks.row06,RHBatch01New256Block39Checks.row07,RHBatch01New256Block39Checks.row08,RHBatch01New256Block39Checks.row09,RHBatch01New256Block39Checks.row10,RHBatch01New256Block39Checks.row11,RHBatch01New256Block39Checks.row12,RHBatch01New256Block39Checks.row13,RHBatch01New256Block39Checks.row14,RHBatch01New256Block39Checks.row15,RHBatch01New256Block39Checks.row16,RHBatch01New256Block39Checks.row17,RHBatch01New256Block39Checks.row18,RHBatch01New256Block39Checks.row19,RHBatch01New256Block39Checks.row20,RHBatch01New256Block39Checks.row21,RHBatch01New256Block39Checks.row22,RHBatch01New256Block39Checks.row23,RHBatch01New256Block39Checks.row24,RHBatch01New256Block39Checks.row25,RHBatch01New256Block39Checks.row26,RHBatch01New256Block39Checks.row27,RHBatch01New256Block39Checks.row28,RHBatch01New256Block39Checks.row29,RHBatch01New256Block39Checks.row30,RHBatch01New256Block39Checks.row31]
#print axioms solution

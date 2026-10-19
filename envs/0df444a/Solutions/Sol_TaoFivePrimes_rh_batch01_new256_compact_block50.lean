-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block50
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:31:14.799907+00:00
-- url     : https://prove2.me/submissions/fa97231d-0fc2-465c-842a-8129113c4853

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block50Checks
theorem row00 : RHBatch01New256CompactReference.checked (1600+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1600+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1600+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1600+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1600+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1600+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1600+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1600+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1600+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1600+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1600+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1600+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1600+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1600+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1600+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1600+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1600+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1600+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1600+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1600+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1600+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1600+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1600+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1600+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1600+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1600+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1600+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1600+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1600+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1600+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1600+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1600+31)=true := by decide +kernel
end RHBatch01New256Block50Checks

theorem solution : RHBatch01New256CompactReference.block 1600 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block50Checks.row00,RHBatch01New256Block50Checks.row01,RHBatch01New256Block50Checks.row02,RHBatch01New256Block50Checks.row03,RHBatch01New256Block50Checks.row04,RHBatch01New256Block50Checks.row05,RHBatch01New256Block50Checks.row06,RHBatch01New256Block50Checks.row07,RHBatch01New256Block50Checks.row08,RHBatch01New256Block50Checks.row09,RHBatch01New256Block50Checks.row10,RHBatch01New256Block50Checks.row11,RHBatch01New256Block50Checks.row12,RHBatch01New256Block50Checks.row13,RHBatch01New256Block50Checks.row14,RHBatch01New256Block50Checks.row15,RHBatch01New256Block50Checks.row16,RHBatch01New256Block50Checks.row17,RHBatch01New256Block50Checks.row18,RHBatch01New256Block50Checks.row19,RHBatch01New256Block50Checks.row20,RHBatch01New256Block50Checks.row21,RHBatch01New256Block50Checks.row22,RHBatch01New256Block50Checks.row23,RHBatch01New256Block50Checks.row24,RHBatch01New256Block50Checks.row25,RHBatch01New256Block50Checks.row26,RHBatch01New256Block50Checks.row27,RHBatch01New256Block50Checks.row28,RHBatch01New256Block50Checks.row29,RHBatch01New256Block50Checks.row30,RHBatch01New256Block50Checks.row31]
#print axioms solution

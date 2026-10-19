-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block34
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:07:35.727774+00:00
-- url     : https://prove2.me/submissions/bb8177c7-60c2-4298-a918-118906089acf

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block34Checks
theorem row00 : RHBatch01New256CompactReference.checked (1088+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1088+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1088+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1088+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1088+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1088+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1088+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1088+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1088+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1088+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1088+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1088+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1088+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1088+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1088+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1088+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1088+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1088+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1088+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1088+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1088+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1088+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1088+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1088+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1088+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1088+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1088+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1088+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1088+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1088+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1088+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1088+31)=true := by decide +kernel
end RHBatch01New256Block34Checks

theorem solution : RHBatch01New256CompactReference.block 1088 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block34Checks.row00,RHBatch01New256Block34Checks.row01,RHBatch01New256Block34Checks.row02,RHBatch01New256Block34Checks.row03,RHBatch01New256Block34Checks.row04,RHBatch01New256Block34Checks.row05,RHBatch01New256Block34Checks.row06,RHBatch01New256Block34Checks.row07,RHBatch01New256Block34Checks.row08,RHBatch01New256Block34Checks.row09,RHBatch01New256Block34Checks.row10,RHBatch01New256Block34Checks.row11,RHBatch01New256Block34Checks.row12,RHBatch01New256Block34Checks.row13,RHBatch01New256Block34Checks.row14,RHBatch01New256Block34Checks.row15,RHBatch01New256Block34Checks.row16,RHBatch01New256Block34Checks.row17,RHBatch01New256Block34Checks.row18,RHBatch01New256Block34Checks.row19,RHBatch01New256Block34Checks.row20,RHBatch01New256Block34Checks.row21,RHBatch01New256Block34Checks.row22,RHBatch01New256Block34Checks.row23,RHBatch01New256Block34Checks.row24,RHBatch01New256Block34Checks.row25,RHBatch01New256Block34Checks.row26,RHBatch01New256Block34Checks.row27,RHBatch01New256Block34Checks.row28,RHBatch01New256Block34Checks.row29,RHBatch01New256Block34Checks.row30,RHBatch01New256Block34Checks.row31]
#print axioms solution

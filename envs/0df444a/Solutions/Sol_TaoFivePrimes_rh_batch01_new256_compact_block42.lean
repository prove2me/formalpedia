-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block42
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:20:51.797232+00:00
-- url     : https://prove2.me/submissions/af77f968-e4e2-4202-8264-abe319716313

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block42Checks
theorem row00 : RHBatch01New256CompactReference.checked (1344+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1344+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1344+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1344+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1344+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1344+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1344+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1344+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1344+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1344+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1344+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1344+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1344+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1344+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1344+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1344+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1344+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1344+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1344+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1344+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1344+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1344+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1344+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1344+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1344+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1344+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1344+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1344+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1344+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1344+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1344+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1344+31)=true := by decide +kernel
end RHBatch01New256Block42Checks

theorem solution : RHBatch01New256CompactReference.block 1344 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block42Checks.row00,RHBatch01New256Block42Checks.row01,RHBatch01New256Block42Checks.row02,RHBatch01New256Block42Checks.row03,RHBatch01New256Block42Checks.row04,RHBatch01New256Block42Checks.row05,RHBatch01New256Block42Checks.row06,RHBatch01New256Block42Checks.row07,RHBatch01New256Block42Checks.row08,RHBatch01New256Block42Checks.row09,RHBatch01New256Block42Checks.row10,RHBatch01New256Block42Checks.row11,RHBatch01New256Block42Checks.row12,RHBatch01New256Block42Checks.row13,RHBatch01New256Block42Checks.row14,RHBatch01New256Block42Checks.row15,RHBatch01New256Block42Checks.row16,RHBatch01New256Block42Checks.row17,RHBatch01New256Block42Checks.row18,RHBatch01New256Block42Checks.row19,RHBatch01New256Block42Checks.row20,RHBatch01New256Block42Checks.row21,RHBatch01New256Block42Checks.row22,RHBatch01New256Block42Checks.row23,RHBatch01New256Block42Checks.row24,RHBatch01New256Block42Checks.row25,RHBatch01New256Block42Checks.row26,RHBatch01New256Block42Checks.row27,RHBatch01New256Block42Checks.row28,RHBatch01New256Block42Checks.row29,RHBatch01New256Block42Checks.row30,RHBatch01New256Block42Checks.row31]
#print axioms solution

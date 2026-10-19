-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block07
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:40:14.59231+00:00
-- url     : https://prove2.me/submissions/dd25cb93-52a1-46dc-8184-65b1700a9a27

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block07Checks
theorem row00 : RHBatch01New256CompactReference.checked (224+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (224+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (224+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (224+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (224+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (224+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (224+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (224+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (224+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (224+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (224+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (224+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (224+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (224+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (224+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (224+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (224+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (224+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (224+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (224+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (224+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (224+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (224+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (224+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (224+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (224+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (224+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (224+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (224+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (224+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (224+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (224+31)=true := by decide +kernel
end RHBatch01New256Block07Checks

theorem solution : RHBatch01New256CompactReference.block 224 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block07Checks.row00,RHBatch01New256Block07Checks.row01,RHBatch01New256Block07Checks.row02,RHBatch01New256Block07Checks.row03,RHBatch01New256Block07Checks.row04,RHBatch01New256Block07Checks.row05,RHBatch01New256Block07Checks.row06,RHBatch01New256Block07Checks.row07,RHBatch01New256Block07Checks.row08,RHBatch01New256Block07Checks.row09,RHBatch01New256Block07Checks.row10,RHBatch01New256Block07Checks.row11,RHBatch01New256Block07Checks.row12,RHBatch01New256Block07Checks.row13,RHBatch01New256Block07Checks.row14,RHBatch01New256Block07Checks.row15,RHBatch01New256Block07Checks.row16,RHBatch01New256Block07Checks.row17,RHBatch01New256Block07Checks.row18,RHBatch01New256Block07Checks.row19,RHBatch01New256Block07Checks.row20,RHBatch01New256Block07Checks.row21,RHBatch01New256Block07Checks.row22,RHBatch01New256Block07Checks.row23,RHBatch01New256Block07Checks.row24,RHBatch01New256Block07Checks.row25,RHBatch01New256Block07Checks.row26,RHBatch01New256Block07Checks.row27,RHBatch01New256Block07Checks.row28,RHBatch01New256Block07Checks.row29,RHBatch01New256Block07Checks.row30,RHBatch01New256Block07Checks.row31]
#print axioms solution

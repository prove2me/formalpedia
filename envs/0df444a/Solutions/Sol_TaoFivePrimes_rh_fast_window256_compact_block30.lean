-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block30
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:04:14.299107+00:00
-- url     : https://prove2.me/submissions/581f66be-96ff-4392-8379-bd3f175e2f57

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock30Checks
theorem row00 : RHFastWindow256CompactReference.checked (960+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (960+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (960+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (960+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (960+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (960+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (960+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (960+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (960+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (960+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (960+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (960+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (960+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (960+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (960+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (960+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (960+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (960+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (960+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (960+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (960+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (960+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (960+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (960+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (960+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (960+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (960+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (960+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (960+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (960+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (960+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (960+31)=true := by decide +kernel
end RHFastWindow256CompactBlock30Checks

theorem solution : RHFastWindow256CompactReference.block 960 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock30Checks.row00,
  RHFastWindow256CompactBlock30Checks.row01,
  RHFastWindow256CompactBlock30Checks.row02,
  RHFastWindow256CompactBlock30Checks.row03,
  RHFastWindow256CompactBlock30Checks.row04,
  RHFastWindow256CompactBlock30Checks.row05,
  RHFastWindow256CompactBlock30Checks.row06,
  RHFastWindow256CompactBlock30Checks.row07,
  RHFastWindow256CompactBlock30Checks.row08,
  RHFastWindow256CompactBlock30Checks.row09,
  RHFastWindow256CompactBlock30Checks.row10,
  RHFastWindow256CompactBlock30Checks.row11,
  RHFastWindow256CompactBlock30Checks.row12,
  RHFastWindow256CompactBlock30Checks.row13,
  RHFastWindow256CompactBlock30Checks.row14,
  RHFastWindow256CompactBlock30Checks.row15,
  RHFastWindow256CompactBlock30Checks.row16,
  RHFastWindow256CompactBlock30Checks.row17,
  RHFastWindow256CompactBlock30Checks.row18,
  RHFastWindow256CompactBlock30Checks.row19,
  RHFastWindow256CompactBlock30Checks.row20,
  RHFastWindow256CompactBlock30Checks.row21,
  RHFastWindow256CompactBlock30Checks.row22,
  RHFastWindow256CompactBlock30Checks.row23,
  RHFastWindow256CompactBlock30Checks.row24,
  RHFastWindow256CompactBlock30Checks.row25,
  RHFastWindow256CompactBlock30Checks.row26,
  RHFastWindow256CompactBlock30Checks.row27,
  RHFastWindow256CompactBlock30Checks.row28,
  RHFastWindow256CompactBlock30Checks.row29,
  RHFastWindow256CompactBlock30Checks.row30,
  RHFastWindow256CompactBlock30Checks.row31]
#print axioms solution

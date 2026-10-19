-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block46
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:20:00.296935+00:00
-- url     : https://prove2.me/submissions/97825ef3-5d18-4a5b-8fb9-af4d07aefc20

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock46Checks
theorem row00 : RHFastWindow256CompactReference.checked (1472+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1472+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1472+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1472+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1472+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1472+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1472+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1472+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1472+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1472+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1472+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1472+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1472+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1472+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1472+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1472+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1472+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1472+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1472+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1472+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1472+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1472+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1472+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1472+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1472+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1472+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1472+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1472+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1472+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1472+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1472+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1472+31)=true := by decide +kernel
end RHFastWindow256CompactBlock46Checks

theorem solution : RHFastWindow256CompactReference.block 1472 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock46Checks.row00,
  RHFastWindow256CompactBlock46Checks.row01,
  RHFastWindow256CompactBlock46Checks.row02,
  RHFastWindow256CompactBlock46Checks.row03,
  RHFastWindow256CompactBlock46Checks.row04,
  RHFastWindow256CompactBlock46Checks.row05,
  RHFastWindow256CompactBlock46Checks.row06,
  RHFastWindow256CompactBlock46Checks.row07,
  RHFastWindow256CompactBlock46Checks.row08,
  RHFastWindow256CompactBlock46Checks.row09,
  RHFastWindow256CompactBlock46Checks.row10,
  RHFastWindow256CompactBlock46Checks.row11,
  RHFastWindow256CompactBlock46Checks.row12,
  RHFastWindow256CompactBlock46Checks.row13,
  RHFastWindow256CompactBlock46Checks.row14,
  RHFastWindow256CompactBlock46Checks.row15,
  RHFastWindow256CompactBlock46Checks.row16,
  RHFastWindow256CompactBlock46Checks.row17,
  RHFastWindow256CompactBlock46Checks.row18,
  RHFastWindow256CompactBlock46Checks.row19,
  RHFastWindow256CompactBlock46Checks.row20,
  RHFastWindow256CompactBlock46Checks.row21,
  RHFastWindow256CompactBlock46Checks.row22,
  RHFastWindow256CompactBlock46Checks.row23,
  RHFastWindow256CompactBlock46Checks.row24,
  RHFastWindow256CompactBlock46Checks.row25,
  RHFastWindow256CompactBlock46Checks.row26,
  RHFastWindow256CompactBlock46Checks.row27,
  RHFastWindow256CompactBlock46Checks.row28,
  RHFastWindow256CompactBlock46Checks.row29,
  RHFastWindow256CompactBlock46Checks.row30,
  RHFastWindow256CompactBlock46Checks.row31]
#print axioms solution

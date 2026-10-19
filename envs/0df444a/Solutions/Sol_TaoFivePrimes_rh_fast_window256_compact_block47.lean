-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block47
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:20:26.605322+00:00
-- url     : https://prove2.me/submissions/5e695b9d-0bef-437f-9c45-92c125ca7a44

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock47Checks
theorem row00 : RHFastWindow256CompactReference.checked (1504+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1504+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1504+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1504+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1504+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1504+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1504+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1504+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1504+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1504+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1504+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1504+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1504+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1504+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1504+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1504+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1504+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1504+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1504+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1504+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1504+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1504+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1504+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1504+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1504+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1504+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1504+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1504+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1504+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1504+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1504+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1504+31)=true := by decide +kernel
end RHFastWindow256CompactBlock47Checks

theorem solution : RHFastWindow256CompactReference.block 1504 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock47Checks.row00,
  RHFastWindow256CompactBlock47Checks.row01,
  RHFastWindow256CompactBlock47Checks.row02,
  RHFastWindow256CompactBlock47Checks.row03,
  RHFastWindow256CompactBlock47Checks.row04,
  RHFastWindow256CompactBlock47Checks.row05,
  RHFastWindow256CompactBlock47Checks.row06,
  RHFastWindow256CompactBlock47Checks.row07,
  RHFastWindow256CompactBlock47Checks.row08,
  RHFastWindow256CompactBlock47Checks.row09,
  RHFastWindow256CompactBlock47Checks.row10,
  RHFastWindow256CompactBlock47Checks.row11,
  RHFastWindow256CompactBlock47Checks.row12,
  RHFastWindow256CompactBlock47Checks.row13,
  RHFastWindow256CompactBlock47Checks.row14,
  RHFastWindow256CompactBlock47Checks.row15,
  RHFastWindow256CompactBlock47Checks.row16,
  RHFastWindow256CompactBlock47Checks.row17,
  RHFastWindow256CompactBlock47Checks.row18,
  RHFastWindow256CompactBlock47Checks.row19,
  RHFastWindow256CompactBlock47Checks.row20,
  RHFastWindow256CompactBlock47Checks.row21,
  RHFastWindow256CompactBlock47Checks.row22,
  RHFastWindow256CompactBlock47Checks.row23,
  RHFastWindow256CompactBlock47Checks.row24,
  RHFastWindow256CompactBlock47Checks.row25,
  RHFastWindow256CompactBlock47Checks.row26,
  RHFastWindow256CompactBlock47Checks.row27,
  RHFastWindow256CompactBlock47Checks.row28,
  RHFastWindow256CompactBlock47Checks.row29,
  RHFastWindow256CompactBlock47Checks.row30,
  RHFastWindow256CompactBlock47Checks.row31]
#print axioms solution

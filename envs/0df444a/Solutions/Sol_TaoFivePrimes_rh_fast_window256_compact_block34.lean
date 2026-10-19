-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block34
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:07:52.665986+00:00
-- url     : https://prove2.me/submissions/5799855c-481b-47e7-991b-12d34cb161ab

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock34Checks
theorem row00 : RHFastWindow256CompactReference.checked (1088+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1088+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1088+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1088+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1088+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1088+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1088+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1088+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1088+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1088+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1088+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1088+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1088+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1088+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1088+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1088+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1088+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1088+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1088+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1088+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1088+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1088+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1088+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1088+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1088+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1088+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1088+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1088+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1088+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1088+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1088+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1088+31)=true := by decide +kernel
end RHFastWindow256CompactBlock34Checks

theorem solution : RHFastWindow256CompactReference.block 1088 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock34Checks.row00,
  RHFastWindow256CompactBlock34Checks.row01,
  RHFastWindow256CompactBlock34Checks.row02,
  RHFastWindow256CompactBlock34Checks.row03,
  RHFastWindow256CompactBlock34Checks.row04,
  RHFastWindow256CompactBlock34Checks.row05,
  RHFastWindow256CompactBlock34Checks.row06,
  RHFastWindow256CompactBlock34Checks.row07,
  RHFastWindow256CompactBlock34Checks.row08,
  RHFastWindow256CompactBlock34Checks.row09,
  RHFastWindow256CompactBlock34Checks.row10,
  RHFastWindow256CompactBlock34Checks.row11,
  RHFastWindow256CompactBlock34Checks.row12,
  RHFastWindow256CompactBlock34Checks.row13,
  RHFastWindow256CompactBlock34Checks.row14,
  RHFastWindow256CompactBlock34Checks.row15,
  RHFastWindow256CompactBlock34Checks.row16,
  RHFastWindow256CompactBlock34Checks.row17,
  RHFastWindow256CompactBlock34Checks.row18,
  RHFastWindow256CompactBlock34Checks.row19,
  RHFastWindow256CompactBlock34Checks.row20,
  RHFastWindow256CompactBlock34Checks.row21,
  RHFastWindow256CompactBlock34Checks.row22,
  RHFastWindow256CompactBlock34Checks.row23,
  RHFastWindow256CompactBlock34Checks.row24,
  RHFastWindow256CompactBlock34Checks.row25,
  RHFastWindow256CompactBlock34Checks.row26,
  RHFastWindow256CompactBlock34Checks.row27,
  RHFastWindow256CompactBlock34Checks.row28,
  RHFastWindow256CompactBlock34Checks.row29,
  RHFastWindow256CompactBlock34Checks.row30,
  RHFastWindow256CompactBlock34Checks.row31]
#print axioms solution

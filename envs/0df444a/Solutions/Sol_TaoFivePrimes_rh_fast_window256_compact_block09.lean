-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block09
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:41:47.936854+00:00
-- url     : https://prove2.me/submissions/05a87520-31cf-4b8c-bcbf-1a76a577bdce

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock09Checks
theorem row00 : RHFastWindow256CompactReference.checked (288+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (288+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (288+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (288+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (288+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (288+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (288+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (288+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (288+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (288+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (288+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (288+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (288+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (288+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (288+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (288+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (288+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (288+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (288+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (288+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (288+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (288+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (288+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (288+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (288+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (288+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (288+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (288+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (288+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (288+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (288+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (288+31)=true := by decide +kernel
end RHFastWindow256CompactBlock09Checks

theorem solution : RHFastWindow256CompactReference.block 288 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock09Checks.row00,
  RHFastWindow256CompactBlock09Checks.row01,
  RHFastWindow256CompactBlock09Checks.row02,
  RHFastWindow256CompactBlock09Checks.row03,
  RHFastWindow256CompactBlock09Checks.row04,
  RHFastWindow256CompactBlock09Checks.row05,
  RHFastWindow256CompactBlock09Checks.row06,
  RHFastWindow256CompactBlock09Checks.row07,
  RHFastWindow256CompactBlock09Checks.row08,
  RHFastWindow256CompactBlock09Checks.row09,
  RHFastWindow256CompactBlock09Checks.row10,
  RHFastWindow256CompactBlock09Checks.row11,
  RHFastWindow256CompactBlock09Checks.row12,
  RHFastWindow256CompactBlock09Checks.row13,
  RHFastWindow256CompactBlock09Checks.row14,
  RHFastWindow256CompactBlock09Checks.row15,
  RHFastWindow256CompactBlock09Checks.row16,
  RHFastWindow256CompactBlock09Checks.row17,
  RHFastWindow256CompactBlock09Checks.row18,
  RHFastWindow256CompactBlock09Checks.row19,
  RHFastWindow256CompactBlock09Checks.row20,
  RHFastWindow256CompactBlock09Checks.row21,
  RHFastWindow256CompactBlock09Checks.row22,
  RHFastWindow256CompactBlock09Checks.row23,
  RHFastWindow256CompactBlock09Checks.row24,
  RHFastWindow256CompactBlock09Checks.row25,
  RHFastWindow256CompactBlock09Checks.row26,
  RHFastWindow256CompactBlock09Checks.row27,
  RHFastWindow256CompactBlock09Checks.row28,
  RHFastWindow256CompactBlock09Checks.row29,
  RHFastWindow256CompactBlock09Checks.row30,
  RHFastWindow256CompactBlock09Checks.row31]
#print axioms solution

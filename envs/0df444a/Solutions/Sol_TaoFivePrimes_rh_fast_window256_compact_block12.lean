-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block12
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:44:31.633879+00:00
-- url     : https://prove2.me/submissions/cc442f78-e969-42ef-a989-7d194f3d4513

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock12Checks
theorem row00 : RHFastWindow256CompactReference.checked (384+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (384+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (384+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (384+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (384+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (384+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (384+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (384+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (384+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (384+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (384+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (384+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (384+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (384+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (384+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (384+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (384+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (384+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (384+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (384+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (384+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (384+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (384+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (384+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (384+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (384+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (384+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (384+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (384+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (384+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (384+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (384+31)=true := by decide +kernel
end RHFastWindow256CompactBlock12Checks

theorem solution : RHFastWindow256CompactReference.block 384 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock12Checks.row00,
  RHFastWindow256CompactBlock12Checks.row01,
  RHFastWindow256CompactBlock12Checks.row02,
  RHFastWindow256CompactBlock12Checks.row03,
  RHFastWindow256CompactBlock12Checks.row04,
  RHFastWindow256CompactBlock12Checks.row05,
  RHFastWindow256CompactBlock12Checks.row06,
  RHFastWindow256CompactBlock12Checks.row07,
  RHFastWindow256CompactBlock12Checks.row08,
  RHFastWindow256CompactBlock12Checks.row09,
  RHFastWindow256CompactBlock12Checks.row10,
  RHFastWindow256CompactBlock12Checks.row11,
  RHFastWindow256CompactBlock12Checks.row12,
  RHFastWindow256CompactBlock12Checks.row13,
  RHFastWindow256CompactBlock12Checks.row14,
  RHFastWindow256CompactBlock12Checks.row15,
  RHFastWindow256CompactBlock12Checks.row16,
  RHFastWindow256CompactBlock12Checks.row17,
  RHFastWindow256CompactBlock12Checks.row18,
  RHFastWindow256CompactBlock12Checks.row19,
  RHFastWindow256CompactBlock12Checks.row20,
  RHFastWindow256CompactBlock12Checks.row21,
  RHFastWindow256CompactBlock12Checks.row22,
  RHFastWindow256CompactBlock12Checks.row23,
  RHFastWindow256CompactBlock12Checks.row24,
  RHFastWindow256CompactBlock12Checks.row25,
  RHFastWindow256CompactBlock12Checks.row26,
  RHFastWindow256CompactBlock12Checks.row27,
  RHFastWindow256CompactBlock12Checks.row28,
  RHFastWindow256CompactBlock12Checks.row29,
  RHFastWindow256CompactBlock12Checks.row30,
  RHFastWindow256CompactBlock12Checks.row31]
#print axioms solution

-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block31
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:05:06.479859+00:00
-- url     : https://prove2.me/submissions/1d1cde80-d838-43d1-9d08-b8dfc434a39a

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock31Checks
theorem row00 : RHFastWindow256CompactReference.checked (992+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (992+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (992+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (992+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (992+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (992+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (992+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (992+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (992+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (992+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (992+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (992+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (992+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (992+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (992+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (992+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (992+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (992+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (992+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (992+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (992+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (992+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (992+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (992+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (992+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (992+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (992+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (992+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (992+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (992+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (992+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (992+31)=true := by decide +kernel
end RHFastWindow256CompactBlock31Checks

theorem solution : RHFastWindow256CompactReference.block 992 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock31Checks.row00,
  RHFastWindow256CompactBlock31Checks.row01,
  RHFastWindow256CompactBlock31Checks.row02,
  RHFastWindow256CompactBlock31Checks.row03,
  RHFastWindow256CompactBlock31Checks.row04,
  RHFastWindow256CompactBlock31Checks.row05,
  RHFastWindow256CompactBlock31Checks.row06,
  RHFastWindow256CompactBlock31Checks.row07,
  RHFastWindow256CompactBlock31Checks.row08,
  RHFastWindow256CompactBlock31Checks.row09,
  RHFastWindow256CompactBlock31Checks.row10,
  RHFastWindow256CompactBlock31Checks.row11,
  RHFastWindow256CompactBlock31Checks.row12,
  RHFastWindow256CompactBlock31Checks.row13,
  RHFastWindow256CompactBlock31Checks.row14,
  RHFastWindow256CompactBlock31Checks.row15,
  RHFastWindow256CompactBlock31Checks.row16,
  RHFastWindow256CompactBlock31Checks.row17,
  RHFastWindow256CompactBlock31Checks.row18,
  RHFastWindow256CompactBlock31Checks.row19,
  RHFastWindow256CompactBlock31Checks.row20,
  RHFastWindow256CompactBlock31Checks.row21,
  RHFastWindow256CompactBlock31Checks.row22,
  RHFastWindow256CompactBlock31Checks.row23,
  RHFastWindow256CompactBlock31Checks.row24,
  RHFastWindow256CompactBlock31Checks.row25,
  RHFastWindow256CompactBlock31Checks.row26,
  RHFastWindow256CompactBlock31Checks.row27,
  RHFastWindow256CompactBlock31Checks.row28,
  RHFastWindow256CompactBlock31Checks.row29,
  RHFastWindow256CompactBlock31Checks.row30,
  RHFastWindow256CompactBlock31Checks.row31]
#print axioms solution

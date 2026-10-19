-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block14
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:47:42.797064+00:00
-- url     : https://prove2.me/submissions/f15704e1-0cc8-4f0f-b3e9-814c9db616f9

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock14Checks
theorem row00 : RHFastWindow256CompactReference.checked (448+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (448+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (448+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (448+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (448+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (448+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (448+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (448+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (448+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (448+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (448+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (448+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (448+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (448+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (448+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (448+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (448+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (448+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (448+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (448+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (448+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (448+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (448+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (448+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (448+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (448+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (448+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (448+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (448+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (448+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (448+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (448+31)=true := by decide +kernel
end RHFastWindow256CompactBlock14Checks

theorem solution : RHFastWindow256CompactReference.block 448 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock14Checks.row00,
  RHFastWindow256CompactBlock14Checks.row01,
  RHFastWindow256CompactBlock14Checks.row02,
  RHFastWindow256CompactBlock14Checks.row03,
  RHFastWindow256CompactBlock14Checks.row04,
  RHFastWindow256CompactBlock14Checks.row05,
  RHFastWindow256CompactBlock14Checks.row06,
  RHFastWindow256CompactBlock14Checks.row07,
  RHFastWindow256CompactBlock14Checks.row08,
  RHFastWindow256CompactBlock14Checks.row09,
  RHFastWindow256CompactBlock14Checks.row10,
  RHFastWindow256CompactBlock14Checks.row11,
  RHFastWindow256CompactBlock14Checks.row12,
  RHFastWindow256CompactBlock14Checks.row13,
  RHFastWindow256CompactBlock14Checks.row14,
  RHFastWindow256CompactBlock14Checks.row15,
  RHFastWindow256CompactBlock14Checks.row16,
  RHFastWindow256CompactBlock14Checks.row17,
  RHFastWindow256CompactBlock14Checks.row18,
  RHFastWindow256CompactBlock14Checks.row19,
  RHFastWindow256CompactBlock14Checks.row20,
  RHFastWindow256CompactBlock14Checks.row21,
  RHFastWindow256CompactBlock14Checks.row22,
  RHFastWindow256CompactBlock14Checks.row23,
  RHFastWindow256CompactBlock14Checks.row24,
  RHFastWindow256CompactBlock14Checks.row25,
  RHFastWindow256CompactBlock14Checks.row26,
  RHFastWindow256CompactBlock14Checks.row27,
  RHFastWindow256CompactBlock14Checks.row28,
  RHFastWindow256CompactBlock14Checks.row29,
  RHFastWindow256CompactBlock14Checks.row30,
  RHFastWindow256CompactBlock14Checks.row31]
#print axioms solution

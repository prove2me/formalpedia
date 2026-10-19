-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block57
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:29:41.421731+00:00
-- url     : https://prove2.me/submissions/09cb809e-fc58-47ce-838f-b6ef25464ae0

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock57Checks
theorem row00 : RHFastWindow256CompactReference.checked (1824+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1824+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1824+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1824+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1824+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1824+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1824+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1824+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1824+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1824+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1824+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1824+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1824+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1824+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1824+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1824+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1824+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1824+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1824+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1824+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1824+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1824+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1824+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1824+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1824+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1824+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1824+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1824+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1824+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1824+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1824+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1824+31)=true := by decide +kernel
end RHFastWindow256CompactBlock57Checks

theorem solution : RHFastWindow256CompactReference.block 1824 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock57Checks.row00,
  RHFastWindow256CompactBlock57Checks.row01,
  RHFastWindow256CompactBlock57Checks.row02,
  RHFastWindow256CompactBlock57Checks.row03,
  RHFastWindow256CompactBlock57Checks.row04,
  RHFastWindow256CompactBlock57Checks.row05,
  RHFastWindow256CompactBlock57Checks.row06,
  RHFastWindow256CompactBlock57Checks.row07,
  RHFastWindow256CompactBlock57Checks.row08,
  RHFastWindow256CompactBlock57Checks.row09,
  RHFastWindow256CompactBlock57Checks.row10,
  RHFastWindow256CompactBlock57Checks.row11,
  RHFastWindow256CompactBlock57Checks.row12,
  RHFastWindow256CompactBlock57Checks.row13,
  RHFastWindow256CompactBlock57Checks.row14,
  RHFastWindow256CompactBlock57Checks.row15,
  RHFastWindow256CompactBlock57Checks.row16,
  RHFastWindow256CompactBlock57Checks.row17,
  RHFastWindow256CompactBlock57Checks.row18,
  RHFastWindow256CompactBlock57Checks.row19,
  RHFastWindow256CompactBlock57Checks.row20,
  RHFastWindow256CompactBlock57Checks.row21,
  RHFastWindow256CompactBlock57Checks.row22,
  RHFastWindow256CompactBlock57Checks.row23,
  RHFastWindow256CompactBlock57Checks.row24,
  RHFastWindow256CompactBlock57Checks.row25,
  RHFastWindow256CompactBlock57Checks.row26,
  RHFastWindow256CompactBlock57Checks.row27,
  RHFastWindow256CompactBlock57Checks.row28,
  RHFastWindow256CompactBlock57Checks.row29,
  RHFastWindow256CompactBlock57Checks.row30,
  RHFastWindow256CompactBlock57Checks.row31]
#print axioms solution

-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block43
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:16:47.85359+00:00
-- url     : https://prove2.me/submissions/50e00dbb-7325-4345-9443-a340b5cde38a

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock43Checks
theorem row00 : RHFastWindow256CompactReference.checked (1376+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1376+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1376+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1376+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1376+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1376+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1376+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1376+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1376+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1376+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1376+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1376+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1376+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1376+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1376+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1376+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1376+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1376+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1376+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1376+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1376+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1376+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1376+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1376+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1376+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1376+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1376+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1376+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1376+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1376+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1376+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1376+31)=true := by decide +kernel
end RHFastWindow256CompactBlock43Checks

theorem solution : RHFastWindow256CompactReference.block 1376 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock43Checks.row00,
  RHFastWindow256CompactBlock43Checks.row01,
  RHFastWindow256CompactBlock43Checks.row02,
  RHFastWindow256CompactBlock43Checks.row03,
  RHFastWindow256CompactBlock43Checks.row04,
  RHFastWindow256CompactBlock43Checks.row05,
  RHFastWindow256CompactBlock43Checks.row06,
  RHFastWindow256CompactBlock43Checks.row07,
  RHFastWindow256CompactBlock43Checks.row08,
  RHFastWindow256CompactBlock43Checks.row09,
  RHFastWindow256CompactBlock43Checks.row10,
  RHFastWindow256CompactBlock43Checks.row11,
  RHFastWindow256CompactBlock43Checks.row12,
  RHFastWindow256CompactBlock43Checks.row13,
  RHFastWindow256CompactBlock43Checks.row14,
  RHFastWindow256CompactBlock43Checks.row15,
  RHFastWindow256CompactBlock43Checks.row16,
  RHFastWindow256CompactBlock43Checks.row17,
  RHFastWindow256CompactBlock43Checks.row18,
  RHFastWindow256CompactBlock43Checks.row19,
  RHFastWindow256CompactBlock43Checks.row20,
  RHFastWindow256CompactBlock43Checks.row21,
  RHFastWindow256CompactBlock43Checks.row22,
  RHFastWindow256CompactBlock43Checks.row23,
  RHFastWindow256CompactBlock43Checks.row24,
  RHFastWindow256CompactBlock43Checks.row25,
  RHFastWindow256CompactBlock43Checks.row26,
  RHFastWindow256CompactBlock43Checks.row27,
  RHFastWindow256CompactBlock43Checks.row28,
  RHFastWindow256CompactBlock43Checks.row29,
  RHFastWindow256CompactBlock43Checks.row30,
  RHFastWindow256CompactBlock43Checks.row31]
#print axioms solution

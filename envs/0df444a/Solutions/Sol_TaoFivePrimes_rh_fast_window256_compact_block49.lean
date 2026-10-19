-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block49
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:21:51.035886+00:00
-- url     : https://prove2.me/submissions/1e2cec63-efb7-46d1-a529-b30f64906108

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock49Checks
theorem row00 : RHFastWindow256CompactReference.checked (1568+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1568+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1568+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1568+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1568+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1568+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1568+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1568+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1568+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1568+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1568+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1568+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1568+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1568+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1568+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1568+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1568+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1568+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1568+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1568+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1568+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1568+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1568+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1568+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1568+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1568+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1568+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1568+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1568+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1568+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1568+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1568+31)=true := by decide +kernel
end RHFastWindow256CompactBlock49Checks

theorem solution : RHFastWindow256CompactReference.block 1568 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock49Checks.row00,
  RHFastWindow256CompactBlock49Checks.row01,
  RHFastWindow256CompactBlock49Checks.row02,
  RHFastWindow256CompactBlock49Checks.row03,
  RHFastWindow256CompactBlock49Checks.row04,
  RHFastWindow256CompactBlock49Checks.row05,
  RHFastWindow256CompactBlock49Checks.row06,
  RHFastWindow256CompactBlock49Checks.row07,
  RHFastWindow256CompactBlock49Checks.row08,
  RHFastWindow256CompactBlock49Checks.row09,
  RHFastWindow256CompactBlock49Checks.row10,
  RHFastWindow256CompactBlock49Checks.row11,
  RHFastWindow256CompactBlock49Checks.row12,
  RHFastWindow256CompactBlock49Checks.row13,
  RHFastWindow256CompactBlock49Checks.row14,
  RHFastWindow256CompactBlock49Checks.row15,
  RHFastWindow256CompactBlock49Checks.row16,
  RHFastWindow256CompactBlock49Checks.row17,
  RHFastWindow256CompactBlock49Checks.row18,
  RHFastWindow256CompactBlock49Checks.row19,
  RHFastWindow256CompactBlock49Checks.row20,
  RHFastWindow256CompactBlock49Checks.row21,
  RHFastWindow256CompactBlock49Checks.row22,
  RHFastWindow256CompactBlock49Checks.row23,
  RHFastWindow256CompactBlock49Checks.row24,
  RHFastWindow256CompactBlock49Checks.row25,
  RHFastWindow256CompactBlock49Checks.row26,
  RHFastWindow256CompactBlock49Checks.row27,
  RHFastWindow256CompactBlock49Checks.row28,
  RHFastWindow256CompactBlock49Checks.row29,
  RHFastWindow256CompactBlock49Checks.row30,
  RHFastWindow256CompactBlock49Checks.row31]
#print axioms solution

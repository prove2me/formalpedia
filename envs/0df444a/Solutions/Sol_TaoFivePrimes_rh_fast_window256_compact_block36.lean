-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block36
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:09:17.734766+00:00
-- url     : https://prove2.me/submissions/6e6c20a6-3ce2-49f7-8a50-eb93b75fbea2

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock36Checks
theorem row00 : RHFastWindow256CompactReference.checked (1152+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1152+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1152+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1152+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1152+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1152+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1152+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1152+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1152+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1152+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1152+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1152+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1152+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1152+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1152+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1152+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1152+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1152+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1152+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1152+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1152+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1152+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1152+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1152+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1152+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1152+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1152+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1152+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1152+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1152+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1152+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1152+31)=true := by decide +kernel
end RHFastWindow256CompactBlock36Checks

theorem solution : RHFastWindow256CompactReference.block 1152 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock36Checks.row00,
  RHFastWindow256CompactBlock36Checks.row01,
  RHFastWindow256CompactBlock36Checks.row02,
  RHFastWindow256CompactBlock36Checks.row03,
  RHFastWindow256CompactBlock36Checks.row04,
  RHFastWindow256CompactBlock36Checks.row05,
  RHFastWindow256CompactBlock36Checks.row06,
  RHFastWindow256CompactBlock36Checks.row07,
  RHFastWindow256CompactBlock36Checks.row08,
  RHFastWindow256CompactBlock36Checks.row09,
  RHFastWindow256CompactBlock36Checks.row10,
  RHFastWindow256CompactBlock36Checks.row11,
  RHFastWindow256CompactBlock36Checks.row12,
  RHFastWindow256CompactBlock36Checks.row13,
  RHFastWindow256CompactBlock36Checks.row14,
  RHFastWindow256CompactBlock36Checks.row15,
  RHFastWindow256CompactBlock36Checks.row16,
  RHFastWindow256CompactBlock36Checks.row17,
  RHFastWindow256CompactBlock36Checks.row18,
  RHFastWindow256CompactBlock36Checks.row19,
  RHFastWindow256CompactBlock36Checks.row20,
  RHFastWindow256CompactBlock36Checks.row21,
  RHFastWindow256CompactBlock36Checks.row22,
  RHFastWindow256CompactBlock36Checks.row23,
  RHFastWindow256CompactBlock36Checks.row24,
  RHFastWindow256CompactBlock36Checks.row25,
  RHFastWindow256CompactBlock36Checks.row26,
  RHFastWindow256CompactBlock36Checks.row27,
  RHFastWindow256CompactBlock36Checks.row28,
  RHFastWindow256CompactBlock36Checks.row29,
  RHFastWindow256CompactBlock36Checks.row30,
  RHFastWindow256CompactBlock36Checks.row31]
#print axioms solution

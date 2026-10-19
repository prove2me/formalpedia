-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block20
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:55:57.485482+00:00
-- url     : https://prove2.me/submissions/48ed93b2-2244-4197-a894-c9e7c8827a4b

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock20Checks
theorem row00 : RHFastWindow256CompactReference.checked (640+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (640+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (640+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (640+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (640+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (640+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (640+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (640+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (640+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (640+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (640+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (640+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (640+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (640+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (640+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (640+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (640+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (640+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (640+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (640+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (640+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (640+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (640+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (640+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (640+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (640+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (640+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (640+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (640+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (640+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (640+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (640+31)=true := by decide +kernel
end RHFastWindow256CompactBlock20Checks

theorem solution : RHFastWindow256CompactReference.block 640 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock20Checks.row00,
  RHFastWindow256CompactBlock20Checks.row01,
  RHFastWindow256CompactBlock20Checks.row02,
  RHFastWindow256CompactBlock20Checks.row03,
  RHFastWindow256CompactBlock20Checks.row04,
  RHFastWindow256CompactBlock20Checks.row05,
  RHFastWindow256CompactBlock20Checks.row06,
  RHFastWindow256CompactBlock20Checks.row07,
  RHFastWindow256CompactBlock20Checks.row08,
  RHFastWindow256CompactBlock20Checks.row09,
  RHFastWindow256CompactBlock20Checks.row10,
  RHFastWindow256CompactBlock20Checks.row11,
  RHFastWindow256CompactBlock20Checks.row12,
  RHFastWindow256CompactBlock20Checks.row13,
  RHFastWindow256CompactBlock20Checks.row14,
  RHFastWindow256CompactBlock20Checks.row15,
  RHFastWindow256CompactBlock20Checks.row16,
  RHFastWindow256CompactBlock20Checks.row17,
  RHFastWindow256CompactBlock20Checks.row18,
  RHFastWindow256CompactBlock20Checks.row19,
  RHFastWindow256CompactBlock20Checks.row20,
  RHFastWindow256CompactBlock20Checks.row21,
  RHFastWindow256CompactBlock20Checks.row22,
  RHFastWindow256CompactBlock20Checks.row23,
  RHFastWindow256CompactBlock20Checks.row24,
  RHFastWindow256CompactBlock20Checks.row25,
  RHFastWindow256CompactBlock20Checks.row26,
  RHFastWindow256CompactBlock20Checks.row27,
  RHFastWindow256CompactBlock20Checks.row28,
  RHFastWindow256CompactBlock20Checks.row29,
  RHFastWindow256CompactBlock20Checks.row30,
  RHFastWindow256CompactBlock20Checks.row31]
#print axioms solution

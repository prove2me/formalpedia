-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block51
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:24:08.921949+00:00
-- url     : https://prove2.me/submissions/12bf21ff-f7f6-49cc-9406-4246589cbeee

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock51Checks
theorem row00 : RHFastWindow256CompactReference.checked (1632+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1632+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1632+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1632+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1632+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1632+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1632+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1632+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1632+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1632+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1632+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1632+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1632+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1632+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1632+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1632+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1632+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1632+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1632+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1632+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1632+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1632+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1632+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1632+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1632+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1632+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1632+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1632+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1632+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1632+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1632+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1632+31)=true := by decide +kernel
end RHFastWindow256CompactBlock51Checks

theorem solution : RHFastWindow256CompactReference.block 1632 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock51Checks.row00,
  RHFastWindow256CompactBlock51Checks.row01,
  RHFastWindow256CompactBlock51Checks.row02,
  RHFastWindow256CompactBlock51Checks.row03,
  RHFastWindow256CompactBlock51Checks.row04,
  RHFastWindow256CompactBlock51Checks.row05,
  RHFastWindow256CompactBlock51Checks.row06,
  RHFastWindow256CompactBlock51Checks.row07,
  RHFastWindow256CompactBlock51Checks.row08,
  RHFastWindow256CompactBlock51Checks.row09,
  RHFastWindow256CompactBlock51Checks.row10,
  RHFastWindow256CompactBlock51Checks.row11,
  RHFastWindow256CompactBlock51Checks.row12,
  RHFastWindow256CompactBlock51Checks.row13,
  RHFastWindow256CompactBlock51Checks.row14,
  RHFastWindow256CompactBlock51Checks.row15,
  RHFastWindow256CompactBlock51Checks.row16,
  RHFastWindow256CompactBlock51Checks.row17,
  RHFastWindow256CompactBlock51Checks.row18,
  RHFastWindow256CompactBlock51Checks.row19,
  RHFastWindow256CompactBlock51Checks.row20,
  RHFastWindow256CompactBlock51Checks.row21,
  RHFastWindow256CompactBlock51Checks.row22,
  RHFastWindow256CompactBlock51Checks.row23,
  RHFastWindow256CompactBlock51Checks.row24,
  RHFastWindow256CompactBlock51Checks.row25,
  RHFastWindow256CompactBlock51Checks.row26,
  RHFastWindow256CompactBlock51Checks.row27,
  RHFastWindow256CompactBlock51Checks.row28,
  RHFastWindow256CompactBlock51Checks.row29,
  RHFastWindow256CompactBlock51Checks.row30,
  RHFastWindow256CompactBlock51Checks.row31]
#print axioms solution

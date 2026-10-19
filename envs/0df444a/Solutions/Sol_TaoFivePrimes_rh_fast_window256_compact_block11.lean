-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block11
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:43:59.596984+00:00
-- url     : https://prove2.me/submissions/bef82452-b468-44e2-a79b-a168f886c429

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock11Checks
theorem row00 : RHFastWindow256CompactReference.checked (352+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (352+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (352+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (352+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (352+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (352+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (352+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (352+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (352+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (352+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (352+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (352+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (352+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (352+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (352+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (352+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (352+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (352+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (352+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (352+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (352+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (352+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (352+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (352+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (352+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (352+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (352+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (352+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (352+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (352+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (352+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (352+31)=true := by decide +kernel
end RHFastWindow256CompactBlock11Checks

theorem solution : RHFastWindow256CompactReference.block 352 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock11Checks.row00,
  RHFastWindow256CompactBlock11Checks.row01,
  RHFastWindow256CompactBlock11Checks.row02,
  RHFastWindow256CompactBlock11Checks.row03,
  RHFastWindow256CompactBlock11Checks.row04,
  RHFastWindow256CompactBlock11Checks.row05,
  RHFastWindow256CompactBlock11Checks.row06,
  RHFastWindow256CompactBlock11Checks.row07,
  RHFastWindow256CompactBlock11Checks.row08,
  RHFastWindow256CompactBlock11Checks.row09,
  RHFastWindow256CompactBlock11Checks.row10,
  RHFastWindow256CompactBlock11Checks.row11,
  RHFastWindow256CompactBlock11Checks.row12,
  RHFastWindow256CompactBlock11Checks.row13,
  RHFastWindow256CompactBlock11Checks.row14,
  RHFastWindow256CompactBlock11Checks.row15,
  RHFastWindow256CompactBlock11Checks.row16,
  RHFastWindow256CompactBlock11Checks.row17,
  RHFastWindow256CompactBlock11Checks.row18,
  RHFastWindow256CompactBlock11Checks.row19,
  RHFastWindow256CompactBlock11Checks.row20,
  RHFastWindow256CompactBlock11Checks.row21,
  RHFastWindow256CompactBlock11Checks.row22,
  RHFastWindow256CompactBlock11Checks.row23,
  RHFastWindow256CompactBlock11Checks.row24,
  RHFastWindow256CompactBlock11Checks.row25,
  RHFastWindow256CompactBlock11Checks.row26,
  RHFastWindow256CompactBlock11Checks.row27,
  RHFastWindow256CompactBlock11Checks.row28,
  RHFastWindow256CompactBlock11Checks.row29,
  RHFastWindow256CompactBlock11Checks.row30,
  RHFastWindow256CompactBlock11Checks.row31]
#print axioms solution

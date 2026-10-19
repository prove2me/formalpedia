-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block17
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:52:46.231998+00:00
-- url     : https://prove2.me/submissions/cbf36a6d-daf5-4d2f-a4e4-692faf9e35ef

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock17Checks
theorem row00 : RHFastWindow256CompactReference.checked (544+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (544+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (544+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (544+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (544+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (544+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (544+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (544+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (544+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (544+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (544+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (544+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (544+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (544+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (544+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (544+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (544+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (544+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (544+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (544+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (544+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (544+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (544+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (544+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (544+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (544+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (544+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (544+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (544+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (544+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (544+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (544+31)=true := by decide +kernel
end RHFastWindow256CompactBlock17Checks

theorem solution : RHFastWindow256CompactReference.block 544 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock17Checks.row00,
  RHFastWindow256CompactBlock17Checks.row01,
  RHFastWindow256CompactBlock17Checks.row02,
  RHFastWindow256CompactBlock17Checks.row03,
  RHFastWindow256CompactBlock17Checks.row04,
  RHFastWindow256CompactBlock17Checks.row05,
  RHFastWindow256CompactBlock17Checks.row06,
  RHFastWindow256CompactBlock17Checks.row07,
  RHFastWindow256CompactBlock17Checks.row08,
  RHFastWindow256CompactBlock17Checks.row09,
  RHFastWindow256CompactBlock17Checks.row10,
  RHFastWindow256CompactBlock17Checks.row11,
  RHFastWindow256CompactBlock17Checks.row12,
  RHFastWindow256CompactBlock17Checks.row13,
  RHFastWindow256CompactBlock17Checks.row14,
  RHFastWindow256CompactBlock17Checks.row15,
  RHFastWindow256CompactBlock17Checks.row16,
  RHFastWindow256CompactBlock17Checks.row17,
  RHFastWindow256CompactBlock17Checks.row18,
  RHFastWindow256CompactBlock17Checks.row19,
  RHFastWindow256CompactBlock17Checks.row20,
  RHFastWindow256CompactBlock17Checks.row21,
  RHFastWindow256CompactBlock17Checks.row22,
  RHFastWindow256CompactBlock17Checks.row23,
  RHFastWindow256CompactBlock17Checks.row24,
  RHFastWindow256CompactBlock17Checks.row25,
  RHFastWindow256CompactBlock17Checks.row26,
  RHFastWindow256CompactBlock17Checks.row27,
  RHFastWindow256CompactBlock17Checks.row28,
  RHFastWindow256CompactBlock17Checks.row29,
  RHFastWindow256CompactBlock17Checks.row30,
  RHFastWindow256CompactBlock17Checks.row31]
#print axioms solution

-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block23
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:57:23.008254+00:00
-- url     : https://prove2.me/submissions/f21ab050-9673-4f4f-8d68-d6f2336b5f2a

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock23Checks
theorem row00 : RHFastWindow256CompactReference.checked (736+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (736+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (736+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (736+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (736+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (736+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (736+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (736+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (736+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (736+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (736+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (736+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (736+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (736+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (736+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (736+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (736+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (736+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (736+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (736+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (736+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (736+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (736+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (736+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (736+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (736+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (736+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (736+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (736+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (736+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (736+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (736+31)=true := by decide +kernel
end RHFastWindow256CompactBlock23Checks

theorem solution : RHFastWindow256CompactReference.block 736 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock23Checks.row00,
  RHFastWindow256CompactBlock23Checks.row01,
  RHFastWindow256CompactBlock23Checks.row02,
  RHFastWindow256CompactBlock23Checks.row03,
  RHFastWindow256CompactBlock23Checks.row04,
  RHFastWindow256CompactBlock23Checks.row05,
  RHFastWindow256CompactBlock23Checks.row06,
  RHFastWindow256CompactBlock23Checks.row07,
  RHFastWindow256CompactBlock23Checks.row08,
  RHFastWindow256CompactBlock23Checks.row09,
  RHFastWindow256CompactBlock23Checks.row10,
  RHFastWindow256CompactBlock23Checks.row11,
  RHFastWindow256CompactBlock23Checks.row12,
  RHFastWindow256CompactBlock23Checks.row13,
  RHFastWindow256CompactBlock23Checks.row14,
  RHFastWindow256CompactBlock23Checks.row15,
  RHFastWindow256CompactBlock23Checks.row16,
  RHFastWindow256CompactBlock23Checks.row17,
  RHFastWindow256CompactBlock23Checks.row18,
  RHFastWindow256CompactBlock23Checks.row19,
  RHFastWindow256CompactBlock23Checks.row20,
  RHFastWindow256CompactBlock23Checks.row21,
  RHFastWindow256CompactBlock23Checks.row22,
  RHFastWindow256CompactBlock23Checks.row23,
  RHFastWindow256CompactBlock23Checks.row24,
  RHFastWindow256CompactBlock23Checks.row25,
  RHFastWindow256CompactBlock23Checks.row26,
  RHFastWindow256CompactBlock23Checks.row27,
  RHFastWindow256CompactBlock23Checks.row28,
  RHFastWindow256CompactBlock23Checks.row29,
  RHFastWindow256CompactBlock23Checks.row30,
  RHFastWindow256CompactBlock23Checks.row31]
#print axioms solution

-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block15
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:48:11.843986+00:00
-- url     : https://prove2.me/submissions/cb253a31-9d39-49b2-9fb2-b35381bb6e5f

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock15Checks
theorem row00 : RHFastWindow256CompactReference.checked (480+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (480+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (480+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (480+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (480+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (480+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (480+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (480+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (480+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (480+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (480+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (480+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (480+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (480+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (480+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (480+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (480+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (480+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (480+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (480+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (480+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (480+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (480+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (480+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (480+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (480+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (480+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (480+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (480+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (480+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (480+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (480+31)=true := by decide +kernel
end RHFastWindow256CompactBlock15Checks

theorem solution : RHFastWindow256CompactReference.block 480 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock15Checks.row00,
  RHFastWindow256CompactBlock15Checks.row01,
  RHFastWindow256CompactBlock15Checks.row02,
  RHFastWindow256CompactBlock15Checks.row03,
  RHFastWindow256CompactBlock15Checks.row04,
  RHFastWindow256CompactBlock15Checks.row05,
  RHFastWindow256CompactBlock15Checks.row06,
  RHFastWindow256CompactBlock15Checks.row07,
  RHFastWindow256CompactBlock15Checks.row08,
  RHFastWindow256CompactBlock15Checks.row09,
  RHFastWindow256CompactBlock15Checks.row10,
  RHFastWindow256CompactBlock15Checks.row11,
  RHFastWindow256CompactBlock15Checks.row12,
  RHFastWindow256CompactBlock15Checks.row13,
  RHFastWindow256CompactBlock15Checks.row14,
  RHFastWindow256CompactBlock15Checks.row15,
  RHFastWindow256CompactBlock15Checks.row16,
  RHFastWindow256CompactBlock15Checks.row17,
  RHFastWindow256CompactBlock15Checks.row18,
  RHFastWindow256CompactBlock15Checks.row19,
  RHFastWindow256CompactBlock15Checks.row20,
  RHFastWindow256CompactBlock15Checks.row21,
  RHFastWindow256CompactBlock15Checks.row22,
  RHFastWindow256CompactBlock15Checks.row23,
  RHFastWindow256CompactBlock15Checks.row24,
  RHFastWindow256CompactBlock15Checks.row25,
  RHFastWindow256CompactBlock15Checks.row26,
  RHFastWindow256CompactBlock15Checks.row27,
  RHFastWindow256CompactBlock15Checks.row28,
  RHFastWindow256CompactBlock15Checks.row29,
  RHFastWindow256CompactBlock15Checks.row30,
  RHFastWindow256CompactBlock15Checks.row31]
#print axioms solution

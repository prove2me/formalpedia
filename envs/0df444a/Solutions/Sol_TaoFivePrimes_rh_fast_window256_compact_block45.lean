-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block45
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:18:38.296401+00:00
-- url     : https://prove2.me/submissions/f848ae1c-06b7-47a6-af76-95325bb0ef78

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock45Checks
theorem row00 : RHFastWindow256CompactReference.checked (1440+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1440+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1440+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1440+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1440+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1440+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1440+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1440+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1440+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1440+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1440+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1440+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1440+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1440+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1440+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1440+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1440+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1440+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1440+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1440+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1440+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1440+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1440+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1440+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1440+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1440+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1440+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1440+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1440+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1440+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1440+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1440+31)=true := by decide +kernel
end RHFastWindow256CompactBlock45Checks

theorem solution : RHFastWindow256CompactReference.block 1440 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock45Checks.row00,
  RHFastWindow256CompactBlock45Checks.row01,
  RHFastWindow256CompactBlock45Checks.row02,
  RHFastWindow256CompactBlock45Checks.row03,
  RHFastWindow256CompactBlock45Checks.row04,
  RHFastWindow256CompactBlock45Checks.row05,
  RHFastWindow256CompactBlock45Checks.row06,
  RHFastWindow256CompactBlock45Checks.row07,
  RHFastWindow256CompactBlock45Checks.row08,
  RHFastWindow256CompactBlock45Checks.row09,
  RHFastWindow256CompactBlock45Checks.row10,
  RHFastWindow256CompactBlock45Checks.row11,
  RHFastWindow256CompactBlock45Checks.row12,
  RHFastWindow256CompactBlock45Checks.row13,
  RHFastWindow256CompactBlock45Checks.row14,
  RHFastWindow256CompactBlock45Checks.row15,
  RHFastWindow256CompactBlock45Checks.row16,
  RHFastWindow256CompactBlock45Checks.row17,
  RHFastWindow256CompactBlock45Checks.row18,
  RHFastWindow256CompactBlock45Checks.row19,
  RHFastWindow256CompactBlock45Checks.row20,
  RHFastWindow256CompactBlock45Checks.row21,
  RHFastWindow256CompactBlock45Checks.row22,
  RHFastWindow256CompactBlock45Checks.row23,
  RHFastWindow256CompactBlock45Checks.row24,
  RHFastWindow256CompactBlock45Checks.row25,
  RHFastWindow256CompactBlock45Checks.row26,
  RHFastWindow256CompactBlock45Checks.row27,
  RHFastWindow256CompactBlock45Checks.row28,
  RHFastWindow256CompactBlock45Checks.row29,
  RHFastWindow256CompactBlock45Checks.row30,
  RHFastWindow256CompactBlock45Checks.row31]
#print axioms solution

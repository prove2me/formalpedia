-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block33
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:06:25.657816+00:00
-- url     : https://prove2.me/submissions/c7e2230c-7c7a-4d03-99fe-e16a0d6a643f

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock33Checks
theorem row00 : RHFastWindow256CompactReference.checked (1056+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1056+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1056+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1056+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1056+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1056+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1056+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1056+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1056+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1056+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1056+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1056+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1056+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1056+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1056+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1056+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1056+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1056+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1056+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1056+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1056+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1056+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1056+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1056+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1056+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1056+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1056+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1056+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1056+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1056+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1056+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1056+31)=true := by decide +kernel
end RHFastWindow256CompactBlock33Checks

theorem solution : RHFastWindow256CompactReference.block 1056 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock33Checks.row00,
  RHFastWindow256CompactBlock33Checks.row01,
  RHFastWindow256CompactBlock33Checks.row02,
  RHFastWindow256CompactBlock33Checks.row03,
  RHFastWindow256CompactBlock33Checks.row04,
  RHFastWindow256CompactBlock33Checks.row05,
  RHFastWindow256CompactBlock33Checks.row06,
  RHFastWindow256CompactBlock33Checks.row07,
  RHFastWindow256CompactBlock33Checks.row08,
  RHFastWindow256CompactBlock33Checks.row09,
  RHFastWindow256CompactBlock33Checks.row10,
  RHFastWindow256CompactBlock33Checks.row11,
  RHFastWindow256CompactBlock33Checks.row12,
  RHFastWindow256CompactBlock33Checks.row13,
  RHFastWindow256CompactBlock33Checks.row14,
  RHFastWindow256CompactBlock33Checks.row15,
  RHFastWindow256CompactBlock33Checks.row16,
  RHFastWindow256CompactBlock33Checks.row17,
  RHFastWindow256CompactBlock33Checks.row18,
  RHFastWindow256CompactBlock33Checks.row19,
  RHFastWindow256CompactBlock33Checks.row20,
  RHFastWindow256CompactBlock33Checks.row21,
  RHFastWindow256CompactBlock33Checks.row22,
  RHFastWindow256CompactBlock33Checks.row23,
  RHFastWindow256CompactBlock33Checks.row24,
  RHFastWindow256CompactBlock33Checks.row25,
  RHFastWindow256CompactBlock33Checks.row26,
  RHFastWindow256CompactBlock33Checks.row27,
  RHFastWindow256CompactBlock33Checks.row28,
  RHFastWindow256CompactBlock33Checks.row29,
  RHFastWindow256CompactBlock33Checks.row30,
  RHFastWindow256CompactBlock33Checks.row31]
#print axioms solution

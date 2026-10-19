-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block22
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:56:54.339246+00:00
-- url     : https://prove2.me/submissions/f8352f64-c390-45c2-8cab-573ca215e227

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock22Checks
theorem row00 : RHFastWindow256CompactReference.checked (704+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (704+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (704+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (704+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (704+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (704+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (704+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (704+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (704+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (704+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (704+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (704+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (704+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (704+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (704+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (704+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (704+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (704+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (704+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (704+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (704+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (704+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (704+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (704+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (704+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (704+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (704+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (704+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (704+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (704+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (704+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (704+31)=true := by decide +kernel
end RHFastWindow256CompactBlock22Checks

theorem solution : RHFastWindow256CompactReference.block 704 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock22Checks.row00,
  RHFastWindow256CompactBlock22Checks.row01,
  RHFastWindow256CompactBlock22Checks.row02,
  RHFastWindow256CompactBlock22Checks.row03,
  RHFastWindow256CompactBlock22Checks.row04,
  RHFastWindow256CompactBlock22Checks.row05,
  RHFastWindow256CompactBlock22Checks.row06,
  RHFastWindow256CompactBlock22Checks.row07,
  RHFastWindow256CompactBlock22Checks.row08,
  RHFastWindow256CompactBlock22Checks.row09,
  RHFastWindow256CompactBlock22Checks.row10,
  RHFastWindow256CompactBlock22Checks.row11,
  RHFastWindow256CompactBlock22Checks.row12,
  RHFastWindow256CompactBlock22Checks.row13,
  RHFastWindow256CompactBlock22Checks.row14,
  RHFastWindow256CompactBlock22Checks.row15,
  RHFastWindow256CompactBlock22Checks.row16,
  RHFastWindow256CompactBlock22Checks.row17,
  RHFastWindow256CompactBlock22Checks.row18,
  RHFastWindow256CompactBlock22Checks.row19,
  RHFastWindow256CompactBlock22Checks.row20,
  RHFastWindow256CompactBlock22Checks.row21,
  RHFastWindow256CompactBlock22Checks.row22,
  RHFastWindow256CompactBlock22Checks.row23,
  RHFastWindow256CompactBlock22Checks.row24,
  RHFastWindow256CompactBlock22Checks.row25,
  RHFastWindow256CompactBlock22Checks.row26,
  RHFastWindow256CompactBlock22Checks.row27,
  RHFastWindow256CompactBlock22Checks.row28,
  RHFastWindow256CompactBlock22Checks.row29,
  RHFastWindow256CompactBlock22Checks.row30,
  RHFastWindow256CompactBlock22Checks.row31]
#print axioms solution

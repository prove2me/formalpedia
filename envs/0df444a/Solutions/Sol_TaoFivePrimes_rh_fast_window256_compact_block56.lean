-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block56
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:28:42.100163+00:00
-- url     : https://prove2.me/submissions/b43d7ca3-6124-485d-b6c0-d9e7913ef664

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock56Checks
theorem row00 : RHFastWindow256CompactReference.checked (1792+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1792+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1792+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1792+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1792+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1792+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1792+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1792+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1792+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1792+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1792+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1792+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1792+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1792+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1792+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1792+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1792+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1792+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1792+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1792+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1792+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1792+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1792+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1792+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1792+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1792+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1792+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1792+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1792+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1792+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1792+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1792+31)=true := by decide +kernel
end RHFastWindow256CompactBlock56Checks

theorem solution : RHFastWindow256CompactReference.block 1792 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock56Checks.row00,
  RHFastWindow256CompactBlock56Checks.row01,
  RHFastWindow256CompactBlock56Checks.row02,
  RHFastWindow256CompactBlock56Checks.row03,
  RHFastWindow256CompactBlock56Checks.row04,
  RHFastWindow256CompactBlock56Checks.row05,
  RHFastWindow256CompactBlock56Checks.row06,
  RHFastWindow256CompactBlock56Checks.row07,
  RHFastWindow256CompactBlock56Checks.row08,
  RHFastWindow256CompactBlock56Checks.row09,
  RHFastWindow256CompactBlock56Checks.row10,
  RHFastWindow256CompactBlock56Checks.row11,
  RHFastWindow256CompactBlock56Checks.row12,
  RHFastWindow256CompactBlock56Checks.row13,
  RHFastWindow256CompactBlock56Checks.row14,
  RHFastWindow256CompactBlock56Checks.row15,
  RHFastWindow256CompactBlock56Checks.row16,
  RHFastWindow256CompactBlock56Checks.row17,
  RHFastWindow256CompactBlock56Checks.row18,
  RHFastWindow256CompactBlock56Checks.row19,
  RHFastWindow256CompactBlock56Checks.row20,
  RHFastWindow256CompactBlock56Checks.row21,
  RHFastWindow256CompactBlock56Checks.row22,
  RHFastWindow256CompactBlock56Checks.row23,
  RHFastWindow256CompactBlock56Checks.row24,
  RHFastWindow256CompactBlock56Checks.row25,
  RHFastWindow256CompactBlock56Checks.row26,
  RHFastWindow256CompactBlock56Checks.row27,
  RHFastWindow256CompactBlock56Checks.row28,
  RHFastWindow256CompactBlock56Checks.row29,
  RHFastWindow256CompactBlock56Checks.row30,
  RHFastWindow256CompactBlock56Checks.row31]
#print axioms solution

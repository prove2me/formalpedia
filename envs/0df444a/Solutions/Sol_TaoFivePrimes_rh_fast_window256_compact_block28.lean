-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block28
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:02:23.584652+00:00
-- url     : https://prove2.me/submissions/86d52822-e76b-4afc-8ba7-371ea5500912

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock28Checks
theorem row00 : RHFastWindow256CompactReference.checked (896+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (896+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (896+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (896+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (896+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (896+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (896+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (896+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (896+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (896+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (896+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (896+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (896+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (896+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (896+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (896+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (896+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (896+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (896+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (896+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (896+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (896+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (896+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (896+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (896+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (896+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (896+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (896+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (896+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (896+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (896+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (896+31)=true := by decide +kernel
end RHFastWindow256CompactBlock28Checks

theorem solution : RHFastWindow256CompactReference.block 896 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock28Checks.row00,
  RHFastWindow256CompactBlock28Checks.row01,
  RHFastWindow256CompactBlock28Checks.row02,
  RHFastWindow256CompactBlock28Checks.row03,
  RHFastWindow256CompactBlock28Checks.row04,
  RHFastWindow256CompactBlock28Checks.row05,
  RHFastWindow256CompactBlock28Checks.row06,
  RHFastWindow256CompactBlock28Checks.row07,
  RHFastWindow256CompactBlock28Checks.row08,
  RHFastWindow256CompactBlock28Checks.row09,
  RHFastWindow256CompactBlock28Checks.row10,
  RHFastWindow256CompactBlock28Checks.row11,
  RHFastWindow256CompactBlock28Checks.row12,
  RHFastWindow256CompactBlock28Checks.row13,
  RHFastWindow256CompactBlock28Checks.row14,
  RHFastWindow256CompactBlock28Checks.row15,
  RHFastWindow256CompactBlock28Checks.row16,
  RHFastWindow256CompactBlock28Checks.row17,
  RHFastWindow256CompactBlock28Checks.row18,
  RHFastWindow256CompactBlock28Checks.row19,
  RHFastWindow256CompactBlock28Checks.row20,
  RHFastWindow256CompactBlock28Checks.row21,
  RHFastWindow256CompactBlock28Checks.row22,
  RHFastWindow256CompactBlock28Checks.row23,
  RHFastWindow256CompactBlock28Checks.row24,
  RHFastWindow256CompactBlock28Checks.row25,
  RHFastWindow256CompactBlock28Checks.row26,
  RHFastWindow256CompactBlock28Checks.row27,
  RHFastWindow256CompactBlock28Checks.row28,
  RHFastWindow256CompactBlock28Checks.row29,
  RHFastWindow256CompactBlock28Checks.row30,
  RHFastWindow256CompactBlock28Checks.row31]
#print axioms solution

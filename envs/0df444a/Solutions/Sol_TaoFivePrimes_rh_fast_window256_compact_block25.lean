-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block25
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:59:13.838561+00:00
-- url     : https://prove2.me/submissions/685d11a7-5aa2-4082-8e0f-5333ec235537

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock25Checks
theorem row00 : RHFastWindow256CompactReference.checked (800+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (800+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (800+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (800+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (800+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (800+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (800+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (800+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (800+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (800+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (800+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (800+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (800+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (800+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (800+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (800+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (800+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (800+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (800+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (800+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (800+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (800+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (800+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (800+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (800+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (800+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (800+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (800+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (800+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (800+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (800+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (800+31)=true := by decide +kernel
end RHFastWindow256CompactBlock25Checks

theorem solution : RHFastWindow256CompactReference.block 800 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock25Checks.row00,
  RHFastWindow256CompactBlock25Checks.row01,
  RHFastWindow256CompactBlock25Checks.row02,
  RHFastWindow256CompactBlock25Checks.row03,
  RHFastWindow256CompactBlock25Checks.row04,
  RHFastWindow256CompactBlock25Checks.row05,
  RHFastWindow256CompactBlock25Checks.row06,
  RHFastWindow256CompactBlock25Checks.row07,
  RHFastWindow256CompactBlock25Checks.row08,
  RHFastWindow256CompactBlock25Checks.row09,
  RHFastWindow256CompactBlock25Checks.row10,
  RHFastWindow256CompactBlock25Checks.row11,
  RHFastWindow256CompactBlock25Checks.row12,
  RHFastWindow256CompactBlock25Checks.row13,
  RHFastWindow256CompactBlock25Checks.row14,
  RHFastWindow256CompactBlock25Checks.row15,
  RHFastWindow256CompactBlock25Checks.row16,
  RHFastWindow256CompactBlock25Checks.row17,
  RHFastWindow256CompactBlock25Checks.row18,
  RHFastWindow256CompactBlock25Checks.row19,
  RHFastWindow256CompactBlock25Checks.row20,
  RHFastWindow256CompactBlock25Checks.row21,
  RHFastWindow256CompactBlock25Checks.row22,
  RHFastWindow256CompactBlock25Checks.row23,
  RHFastWindow256CompactBlock25Checks.row24,
  RHFastWindow256CompactBlock25Checks.row25,
  RHFastWindow256CompactBlock25Checks.row26,
  RHFastWindow256CompactBlock25Checks.row27,
  RHFastWindow256CompactBlock25Checks.row28,
  RHFastWindow256CompactBlock25Checks.row29,
  RHFastWindow256CompactBlock25Checks.row30,
  RHFastWindow256CompactBlock25Checks.row31]
#print axioms solution

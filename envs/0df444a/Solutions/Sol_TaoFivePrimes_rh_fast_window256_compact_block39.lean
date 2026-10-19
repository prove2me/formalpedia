-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block39
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:12:47.43669+00:00
-- url     : https://prove2.me/submissions/bd2b1c69-8fa2-418c-aa64-5e07c65c31f3

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock39Checks
theorem row00 : RHFastWindow256CompactReference.checked (1248+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1248+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1248+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1248+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1248+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1248+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1248+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1248+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1248+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1248+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1248+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1248+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1248+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1248+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1248+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1248+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1248+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1248+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1248+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1248+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1248+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1248+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1248+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1248+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1248+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1248+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1248+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1248+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1248+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1248+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1248+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1248+31)=true := by decide +kernel
end RHFastWindow256CompactBlock39Checks

theorem solution : RHFastWindow256CompactReference.block 1248 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock39Checks.row00,
  RHFastWindow256CompactBlock39Checks.row01,
  RHFastWindow256CompactBlock39Checks.row02,
  RHFastWindow256CompactBlock39Checks.row03,
  RHFastWindow256CompactBlock39Checks.row04,
  RHFastWindow256CompactBlock39Checks.row05,
  RHFastWindow256CompactBlock39Checks.row06,
  RHFastWindow256CompactBlock39Checks.row07,
  RHFastWindow256CompactBlock39Checks.row08,
  RHFastWindow256CompactBlock39Checks.row09,
  RHFastWindow256CompactBlock39Checks.row10,
  RHFastWindow256CompactBlock39Checks.row11,
  RHFastWindow256CompactBlock39Checks.row12,
  RHFastWindow256CompactBlock39Checks.row13,
  RHFastWindow256CompactBlock39Checks.row14,
  RHFastWindow256CompactBlock39Checks.row15,
  RHFastWindow256CompactBlock39Checks.row16,
  RHFastWindow256CompactBlock39Checks.row17,
  RHFastWindow256CompactBlock39Checks.row18,
  RHFastWindow256CompactBlock39Checks.row19,
  RHFastWindow256CompactBlock39Checks.row20,
  RHFastWindow256CompactBlock39Checks.row21,
  RHFastWindow256CompactBlock39Checks.row22,
  RHFastWindow256CompactBlock39Checks.row23,
  RHFastWindow256CompactBlock39Checks.row24,
  RHFastWindow256CompactBlock39Checks.row25,
  RHFastWindow256CompactBlock39Checks.row26,
  RHFastWindow256CompactBlock39Checks.row27,
  RHFastWindow256CompactBlock39Checks.row28,
  RHFastWindow256CompactBlock39Checks.row29,
  RHFastWindow256CompactBlock39Checks.row30,
  RHFastWindow256CompactBlock39Checks.row31]
#print axioms solution

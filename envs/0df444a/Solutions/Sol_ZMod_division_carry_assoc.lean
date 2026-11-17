-- Prove2me | solution 1 for ZMod.division_carry_assoc
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:07.811457+00:00
-- url     : https://prove2.me/submissions/fcd2bee9-d994-4eb5-821f-cdb3d94d41e7

import Mathlib

set_option autoImplicit false

private theorem division_carry_decomposition (a b : ZMod 71) :
    (a + b).val + 71 * ((a.val + b.val) / 71) = a.val + b.val := by
  rw [ZMod.val_add]
  exact Nat.mod_add_div _ _

/-- Integer carries for the standard representatives of residues satisfy associativity. -/
theorem _root_.solution (a b c : ZMod 71) :
    (a.val + b.val) / 71 + ((a + b).val + c.val) / 71 =
      (b.val + c.val) / 71 + (a.val + (b + c).val) / 71 := by
  have hab := division_carry_decomposition a b
  have hbc := division_carry_decomposition b c
  have hl := division_carry_decomposition (a + b) c
  have hr := division_carry_decomposition a (b + c)
  have hi : ((a + b) + c).val = (a + (b + c)).val := by rw [add_assoc]
  omega

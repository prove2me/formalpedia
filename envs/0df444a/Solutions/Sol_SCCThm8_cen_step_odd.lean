-- Prove2me | solution 1 for SCCThm8.cen_step_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:45:59.066167+00:00
-- url     : https://prove2.me/submissions/ab902c86-9fd8-4061-9758-753aec27ad0d

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
public import Theorems.Thm_SCCThm8_choose_odd_step
public import Theorems.Thm_SCCThm8_choose_even_step

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (j : ℕ) :
    (3 * j + 3) * cen (2 * j + 1 + 1) = 4 * (6 * j + 5) * cen (2 * j + 1) := by
  unfold cen
  rw [show 3 * (2 * j + 1 + 1) = 2 * (3 * j + 2) + 2 by ring,
    show (2 * (3 * j + 2) + 2) / 2 = 3 * j + 2 + 1 by omega,
    show 3 * (2 * j + 1) = 2 * (3 * j + 1) + 1 by ring,
    show (2 * (3 * j + 1) + 1) / 2 = 3 * j + 1 by omega]
  have a := choose_even_step (3 * j + 1)
  have b := choose_odd_step (3 * j + 2)
  have c := choose_even_step (3 * j + 2)
  rw [show 2 * (3 * j + 1) + 2 = 2 * (3 * j + 2) by ring,
    show 3 * j + 1 + 1 = 3 * j + 2 by ring] at a
  calc (3 * j + 3) * Nat.choose (2 * (3 * j + 2) + 2) (3 * j + 2 + 1)
      = 2 * (Nat.choose (2 * (3 * j + 2) + 1) (3 * j + 2) * (3 * j + 2 + 1)) := by rw [c]; ring
    _ = 2 * ((2 * (3 * j + 2) + 1) * Nat.choose (2 * (3 * j + 2)) (3 * j + 2)) := by rw [b]
    _ = 4 * (6 * j + 5) * Nat.choose (2 * (3 * j + 1) + 1) (3 * j + 1) := by rw [a]; ring
end SCCThm8

-- Prove2me | solution 1 for SCCThm8.cen_step_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:45:53.577158+00:00
-- url     : https://prove2.me/submissions/53edc81f-f607-44c9-b3f9-667573de3c83

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
    (3 * j + 1) * (3 * j + 2) * cen (2 * j + 1) = 2 * (6 * j + 1) * (6 * j + 3) * cen (2 * j) := by
  unfold cen
  rw [show 3 * (2 * j + 1) = 2 * (3 * j + 1) + 1 by ring,
    show (2 * (3 * j + 1) + 1) / 2 = 3 * j + 1 by omega,
    show 3 * (2 * j) = 2 * (3 * j) by ring, show 2 * (3 * j) / 2 = 3 * j by omega]
  have a := choose_odd_step (3 * j)
  have b := choose_even_step (3 * j)
  have c := choose_odd_step (3 * j + 1)
  rw [show 2 * (3 * j) + 2 = 2 * (3 * j + 1) by ring] at b
  calc (3 * j + 1) * (3 * j + 2) * Nat.choose (2 * (3 * j + 1) + 1) (3 * j + 1)
      = (3 * j + 1) * (Nat.choose (2 * (3 * j + 1) + 1) (3 * j + 1) * (3 * j + 1 + 1)) := by ring
    _ = (3 * j + 1) * ((2 * (3 * j + 1) + 1) * (2 * Nat.choose (2 * (3 * j) + 1) (3 * j))) := by
        rw [c, b]
    _ = 2 * (2 * (3 * j + 1) + 1) * (Nat.choose (2 * (3 * j) + 1) (3 * j) * (3 * j + 1)) := by ring
    _ = 2 * (6 * j + 1) * (6 * j + 3) * Nat.choose (2 * (3 * j)) (3 * j) := by rw [a]; ring
end SCCThm8

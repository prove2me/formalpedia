-- Prove2me | solution 1 for SCCThm8.ratio_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:38.148231+00:00
-- url     : https://prove2.me/submissions/a29c8683-1274-47c2-bf9d-10d861a3818c

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
public import Theorems.Thm_SCCThm8_trin_succ
public import Theorems.Thm_SCCThm8_cen_step_even
public import Theorems.Thm_SCCThm8_cen_step_odd

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (k : ℕ) : 8 * trin (k + 1) * cen k ≤ 27 * cen (k + 1) * trin k := by
  have ht := trin_succ k
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have hc := cen_step_even j
    set a1 := trin (2 * j + 1)
    set a0 := trin (2 * j)
    set c1 := cen (2 * j + 1)
    set c0 := cen (2 * j)
    have hX : 0 < (2 * j + 1) ^ 2 * ((3 * j + 1) * (3 * j + 2)) := by positivity
    apply Nat.le_of_mul_le_mul_left _ hX
    have eL : (2 * j + 1) ^ 2 * ((3 * j + 1) * (3 * j + 2)) * (8 * a1 * c0)
        = 24 * (6 * j + 2) * (6 * j + 1) * ((3 * j + 1) * (3 * j + 2)) * (a0 * c0) := by
      rw [show (2 * j + 1) ^ 2 * ((3 * j + 1) * (3 * j + 2)) * (8 * a1 * c0)
          = 8 * ((3 * j + 1) * (3 * j + 2)) * c0 * ((2 * j + 1) ^ 2 * a1) by ring, ht]
      ring
    have eR : (2 * j + 1) ^ 2 * ((3 * j + 1) * (3 * j + 2)) * (27 * c1 * a0)
        = 54 * (2 * j + 1) ^ 2 * (6 * j + 1) * (6 * j + 3) * (a0 * c0) := by
      rw [show (2 * j + 1) ^ 2 * ((3 * j + 1) * (3 * j + 2)) * (27 * c1 * a0)
          = 27 * (2 * j + 1) ^ 2 * a0 * ((3 * j + 1) * (3 * j + 2) * c1) by ring, hc]
      ring
    rw [eL, eR]
    apply Nat.mul_le_mul_right
    ring_nf; nlinarith
  · have hc := cen_step_odd j
    set a1 := trin (2 * j + 1 + 1)
    set a0 := trin (2 * j + 1)
    set c1 := cen (2 * j + 1 + 1)
    set c0 := cen (2 * j + 1)
    have hX : 0 < (2 * j + 1 + 1) ^ 2 * (3 * j + 3) := by positivity
    apply Nat.le_of_mul_le_mul_left _ hX
    have eL : (2 * j + 1 + 1) ^ 2 * (3 * j + 3) * (8 * a1 * c0)
        = 24 * (6 * j + 5) * (6 * j + 4) * (3 * j + 3) * (a0 * c0) := by
      rw [show (2 * j + 1 + 1) ^ 2 * (3 * j + 3) * (8 * a1 * c0)
          = 8 * (3 * j + 3) * c0 * ((2 * j + 1 + 1) ^ 2 * a1) by ring, ht]
      ring
    have eR : (2 * j + 1 + 1) ^ 2 * (3 * j + 3) * (27 * c1 * a0)
        = 108 * (2 * j + 1 + 1) ^ 2 * (6 * j + 5) * (a0 * c0) := by
      rw [show (2 * j + 1 + 1) ^ 2 * (3 * j + 3) * (27 * c1 * a0)
          = 27 * (2 * j + 1 + 1) ^ 2 * a0 * ((3 * j + 3) * c1) by ring, hc]
      ring
    rw [eL, eR]
    apply Nat.mul_le_mul_right
    ring_nf; nlinarith
end SCCThm8

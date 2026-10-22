-- Prove2me | solution 1 for SphereSOS.Rate.gegenbauer_deriv_one
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:58:22.655833+00:00
-- url     : https://prove2.me/submissions/96137972-d630-4c4b-ae75-f3b965e85d01

import Mathlib
import Definitions.Def_SphereSOS_Rate_Gegenbauer

set_option autoImplicit false
open SphereSOS.Rate

theorem geg_aux (d : ℕ) (hd : 2 ≤ d) (k : ℕ) :
    ((geg d k).eval 1 = 1 ∧
      (geg d k).derivative.eval 1 = (k : ℝ) * ((k : ℝ) + (d : ℝ) - 2) / ((d : ℝ) - 1)) ∧
    ((geg d (k + 1)).eval 1 = 1 ∧
      (geg d (k + 1)).derivative.eval 1 =
        ((k : ℝ) + 1) * (((k : ℝ) + 1) + (d : ℝ) - 2) / ((d : ℝ) - 1)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  induction k with
  | zero =>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp [geg]
    · simp [geg]
    · simp [geg]
    · simp [geg]; field_simp; ring
  | succ k ih =>
    obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩⟩ := ih
    refine ⟨⟨h1, ?_⟩, ?_⟩
    · rw [h1']; push_cast; ring
    · have hk : (k : ℝ) + (d : ℝ) - 1 ≠ 0 := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have hdef : geg d (k + 2) =
          Polynomial.C (1 / ((k : ℝ) + (d : ℝ) - 1)) *
            (Polynomial.C (2 * (k : ℝ) + (d : ℝ)) * Polynomial.X * geg d (k + 1) -
              Polynomial.C ((k : ℝ) + 1) * geg d k) := by
        rw [geg]
      have e1 : (geg d (k + 1 + 1)).eval 1 = 1 := by
        rw [show k + 1 + 1 = k + 2 from rfl, hdef]
        simp [h0, h1]
        field_simp
        ring
      refine ⟨e1, ?_⟩
      rw [show k + 1 + 1 = k + 2 from rfl, hdef]
      simp [Polynomial.derivative_mul, h1, h0', h1']
      push_cast
      field_simp
      ring

theorem solution (d i : ℕ) (hd : 2 ≤ d) :
    (geg d i).derivative.eval 1 = (i : ℝ) * ((i : ℝ) + (d : ℝ) - 2) / ((d : ℝ) - 1) :=
  (geg_aux d hd i).1.2

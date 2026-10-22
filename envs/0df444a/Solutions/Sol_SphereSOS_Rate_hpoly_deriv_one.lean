-- Prove2me | solution 1 for SphereSOS.Rate.hpoly_deriv_one
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:03:13.74166+00:00
-- url     : https://prove2.me/submissions/a03c59fa-44a4-45bd-815c-62f4dec28464

import Mathlib
import Definitions.Def_SphereSOS_Rate_Toeplitz

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

theorem sum_aux (d : ℕ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ((2 * k : ℕ) : ℝ) * (((2 * k : ℕ) : ℝ) + d - 2) =
      (n : ℝ) * (n + 1) * (3 * d + 4 * n - 4) / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

theorem solution (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n) :
    (hpoly d n).derivative.eval 1 =
      ((n : ℝ) + 1) * (3 * (d : ℝ) + 4 * (n : ℝ) - 4) / (3 * ((d : ℝ) - 1)) := by
  unfold hpoly
  rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.derivative_sum,
    Polynomial.eval_finset_sum]
  have h : ∀ k ∈ Finset.Icc 1 n, (geg d (2 * k)).derivative.eval 1 =
      ((2 * k : ℕ) : ℝ) * (((2 * k : ℕ) : ℝ) + d - 2) / ((d : ℝ) - 1) :=
    fun k _ => (geg_aux d hd (2 * k)).1.2
  rw [Finset.sum_congr rfl h, ← Finset.sum_div, sum_aux]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  field_simp

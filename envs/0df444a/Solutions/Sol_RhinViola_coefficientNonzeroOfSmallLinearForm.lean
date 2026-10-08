-- Prove2me | solution 1 for RhinViola.coefficientNonzeroOfSmallLinearForm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T11:29:41.160842+00:00
-- url     : https://prove2.me/submissions/6b4a084a-2bb6-4a70-82db-c34b7a90d68e

import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic

theorem solution
    (α f : ℝ) (a b : ℤ)
    (hf : f = (a : ℝ) - (b : ℝ) * α)
    (hfnz : f ≠ 0) (hsmall : |f| < 1) :
    b ≠ 0 := by
  intro hb
  have hfa : f = (a : ℝ) := by
    rw [hf, hb]
    norm_num
  have hane : a ≠ 0 := by
    intro ha
    apply hfnz
    rw [hfa, ha]
    norm_num
  have haone : (1 : ℤ) ≤ |a| :=
    Int.one_le_abs hane
  have haoneR : (1 : ℝ) ≤ |(a : ℝ)| := by
    have hcast : (1 : ℝ) ≤ ((|a| : ℤ) : ℝ) := by
      exact_mod_cast haone
    simpa only [Int.cast_abs] using hcast
  rw [hfa] at hsmall
  linarith

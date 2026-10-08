-- Prove2me | solution 1 for RhinViola.partialFractionKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T19:44:16.376371+00:00
-- url     : https://prove2.me/submissions/c117f089-f14e-4da6-a143-b02e03185647

import Mathlib.Tactic

theorem solution (h m k : ℕ) (hhm : h < m) :
    (1 : ℝ) /
        ((((k + h + 1 : ℕ) : ℝ)) * (((k + m + 1 : ℕ) : ℝ))) =
      (1 / ((m : ℝ) - (h : ℝ))) *
        ((1 / (((k + h + 1 : ℕ) : ℝ))) -
          (1 / (((k + m + 1 : ℕ) : ℝ)))) := by
  have hmhNat : h ≠ m := ne_of_lt hhm
  have hmh : (m : ℝ) - (h : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hmhNat.symm)
  have hkh : (((k + h + 1 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  have hkm : (((k + m + 1 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  field_simp [hmh, hkh, hkm]
  push_cast
  ring

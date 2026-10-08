-- Prove2me | solution 1 for RhinViola.zeroDeterminantIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T07:55:10.237848+00:00
-- url     : https://prove2.me/submissions/993e6f6d-0980-4435-8443-a2abef6886ea

import Mathlib.Tactic
import Mathlib.Data.Int.Cast.Lemmas

theorem solution
    (α f : ℝ) (a b p : ℤ) (q : ℕ)
    (hq : 0 < q) (hb : b ≠ 0)
    (hf : f = (a : ℝ) - (b : ℝ) * α)
    (hdet : (q : ℤ) * a = p * b) :
    |α - (p : ℝ) / (q : ℝ)| = |f| / |(b : ℝ)| := by
  have hqR : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  have hbR : (b : ℝ) ≠ 0 := by
    exact_mod_cast hb
  have hdetR :
      (q : ℝ) * (a : ℝ) = (p : ℝ) * (b : ℝ) := by
    exact_mod_cast hdet
  have ha :
      (a : ℝ) = (b : ℝ) * (p : ℝ) / (q : ℝ) := by
    field_simp [hqR]
    nlinarith [hdetR]
  have hfexpr :
      f = -(b : ℝ) * (α - (p : ℝ) / (q : ℝ)) := by
    rw [hf, ha]
    ring
  have habsb : |(b : ℝ)| ≠ 0 := abs_ne_zero.mpr hbR
  rw [hfexpr, abs_mul, abs_neg]
  field_simp [habsb]

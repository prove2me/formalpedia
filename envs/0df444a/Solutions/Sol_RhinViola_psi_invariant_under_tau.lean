-- Prove2me | solution 1 for RhinViola.psi_invariant_under_tau
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T21:27:22.283135+00:00
-- url     : https://prove2.me/submissions/5fd2cca5-79ea-474d-9e36-6ad564a2ba6f

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

theorem solution
    (x y : ℂ) (hx : x ≠ 0) (hxy : 1 - x * y ≠ 0) :
    (fun u v : ℂ => u * v * (1 - u) * (1 - v) / (1 - u * v))
      ((1 - x) / (1 - x * y)) (1 - x * y) =
    (fun u v : ℂ => u * v * (1 - u) * (1 - v) / (1 - u * v)) x y := by
  have hprod :
      ((1 - x) / (1 - x * y)) * (1 - x * y) = 1 - x := by
    field_simp [hxy]
  dsimp
  rw [hprod]
  field_simp [hx, hxy]
  <;> ring

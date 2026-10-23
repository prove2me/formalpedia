-- Prove2me | solution 1 for PersPricingDist.UniformA.profit_gap_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:45:33.409726+00:00
-- url     : https://prove2.me/submissions/e95853b8-5f39-4aba-91ec-e43a3efe4638

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting

open PersPricingDist.UniformA

theorem solution (M : Model) (hM : M.Standing) :
    (M.s + 2 * M.s ^ 2 - 4 * M.v * M.s - 2 * M.v * M.s ^ 2 +
      2 * M.v ^ 2 + M.v ^ 2 * M.s) /
        (4 * M.s * (1 - M.s ^ 2)) -
      (M.s * (5 * M.s + 4 - M.s ^ 2) +
        4 * M.v * (1 + M.s) * (M.v - 2 * M.s)) /
        (4 * M.s * (1 - M.s) * (4 + 5 * M.s)) =
      (((M.s - M.v) ^ 2) / (4 * M.s)) *
        ((4 + 6 * M.s + M.s ^ 2) / ((4 + 5 * M.s) * (1 - M.s ^ 2))) ∧
    0 < (((M.s - M.v) ^ 2) / (4 * M.s)) *
        ((4 + 6 * M.s + M.s ^ 2) / ((4 + 5 * M.s) * (1 - M.s ^ 2))) := by
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  have h1 : 0 < 1 - M.s := by linarith
  have h2 : 0 < 1 - M.s ^ 2 := by nlinarith
  have h3 : 0 < 4 + 5 * M.s := by linarith
  have h4 : 0 < 1 + M.s := by linarith
  constructor
  · have e : 1 - M.s ^ 2 = (1 - M.s) * (1 + M.s) := by ring
    rw [e]
    field_simp
    ring
  · have : 0 < (M.s - M.v) ^ 2 := by
      have : M.s - M.v ≠ 0 := by linarith
      positivity
    positivity

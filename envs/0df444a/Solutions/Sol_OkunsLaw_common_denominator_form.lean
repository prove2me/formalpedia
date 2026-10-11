-- Prove2me | solution 1 for OkunsLaw.common_denominator_form
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T19:51:34.237392+00:00
-- url     : https://prove2.me/submissions/acbe6e94-bb79-4b56-9459-79e583fcc534

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OkunsLaw_defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OkunsLaw

theorem solution (c : ℝ) (Y Ybar u ubar : ℕ → ℝ) (t : ℕ)
    (hYbar₀ : 0 < Ybar t) (hYbar₁ : 0 < Ybar (t + 1))
    (h₀ : GapLaw c Y Ybar u ubar t)
    (h₁ : GapLaw c Y Ybar u ubar (t + 1)) :
    (Ybar t * delta Y t - Y t * delta Ybar t) /
       (Ybar t * (Ybar t + delta Ybar t)) =
      c * (delta ubar t - delta u t) := by
  have hz₀ : Ybar t ≠ 0 := ne_of_gt hYbar₀
  have hz₁ : Ybar (t + 1) ≠ 0 := ne_of_gt hYbar₁
  have heq₀ : Y t / Ybar t - 1 = c * (ubar t - u t) := by
    change (Ybar t - Y t) / Ybar t = c * (u t - ubar t) at h₀
    rw [sub_div, div_self hz₀] at h₀
    nlinarith
  have heq₁ : Y (t + 1) / Ybar (t + 1) - 1 =
      c * (ubar (t + 1) - u (t + 1)) := by
    change (Ybar (t + 1) - Y (t + 1)) / Ybar (t + 1) =
      c * (u (t + 1) - ubar (t + 1)) at h₁
    rw [sub_div, div_self hz₁] at h₁
    nlinarith
  have hdiff : Y (t + 1) / Ybar (t + 1) - Y t / Ybar t =
      c * ((ubar (t + 1) - ubar t) - (u (t + 1) - u t)) := by
    nlinarith [heq₀, heq₁]
  change (Ybar t * (Y (t + 1) - Y t) -
    Y t * (Ybar (t + 1) - Ybar t)) /
    (Ybar t * (Ybar t + (Ybar (t + 1) - Ybar t))) =
    c * ((ubar (t + 1) - ubar t) - (u (t + 1) - u t))
  calc
    _ = Y (t + 1) / Ybar (t + 1) - Y t / Ybar t := by
      have hden : Ybar t + (Ybar (t + 1) - Ybar t) =
          Ybar (t + 1) := by ring
      rw [hden]
      field_simp [hz₀, hz₁] <;> ring
    _ = _ := hdiff

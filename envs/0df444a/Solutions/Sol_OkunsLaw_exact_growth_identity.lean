-- Prove2me | solution 1 for OkunsLaw.exact_growth_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T19:52:25.245782+00:00
-- url     : https://prove2.me/submissions/7fd59a52-4752-4ee8-a74d-06c09340428d

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OkunsLaw_defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OkunsLaw

theorem solution (c : ℝ) (Y Ybar u ubar : ℕ → ℝ) (t : ℕ)
    (hY : 0 < Y t) (hYbar₀ : 0 < Ybar t)
    (hYbar₁ : 0 < Ybar (t + 1))
    (h₀ : GapLaw c Y Ybar u ubar t)
    (h₁ : GapLaw c Y Ybar u ubar (t + 1)) :
    growthRate Y t - growthRate Ybar t =
      c * (delta ubar t - delta u t) *
        ((Ybar t + delta Ybar t) / Y t) := by
  have hzY : Y t ≠ 0 := ne_of_gt hY
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
  have hdiff : delta (fun s => Y s / Ybar s) t =
      c * (delta ubar t - delta u t) := by
    dsimp [delta]
    nlinarith [heq₀, heq₁]
  have halg : growthRate Y t - growthRate Ybar t =
      delta (fun s => Y s / Ybar s) t * (Ybar (t + 1) / Y t) := by
    dsimp [growthRate, delta]
    field_simp [hzY, hz₀, hz₁] <;> ring
  have hnext : Ybar t + delta Ybar t = Ybar (t + 1) := by
    dsimp [delta]
    ring
  rw [halg, hdiff, hnext]

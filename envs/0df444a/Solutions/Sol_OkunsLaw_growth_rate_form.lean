-- Prove2me | solution 1 for OkunsLaw.growth_rate_form
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T19:53:25.117137+00:00
-- url     : https://prove2.me/submissions/e4a59a91-fbed-4454-9386-c2369ccbe79e

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OkunsLaw_defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OkunsLaw

private theorem okun_growth_core (c : ℝ) (Y Ybar u ubar : ℕ → ℝ) (t : ℕ)
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

theorem solution (c k : ℝ) (Y Ybar u ubar : ℕ → ℝ) (t : ℕ)
    (hY : 0 < Y t) (hYbar₀ : 0 < Ybar t)
    (hYbar₁ : 0 < Ybar (t + 1))
    (h₀ : GapLaw c Y Ybar u ubar t)
    (h₁ : GapLaw c Y Ybar u ubar (t + 1))
    (hnatural : delta ubar t = 0)
    (hpotential : growthRate Ybar t = k) :
    growthRate Y t =
      k - c * delta u t -
        c * delta u t * ((Ybar t + delta Ybar t) / Y t - 1) := by
  have hcore := okun_growth_core c Y Ybar u ubar t hY hYbar₀ hYbar₁ h₀ h₁
  rw [hpotential, hnatural] at hcore
  calc
    growthRate Y t =
        k - c * delta u t * ((Ybar t + delta Ybar t) / Y t) := by
          nlinarith [hcore]
    _ = k - c * delta u t -
        c * delta u t * ((Ybar t + delta Ybar t) / Y t - 1) := by ring

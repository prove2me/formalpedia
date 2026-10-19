-- Prove2me | solution 1 for SoficGroups.KunRootedUniversalToleranceNumerics.rooted_graph_boundary_lt_of_slow_tolerance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/971354ad-4807-446d-8df0-cd1e1963d79c

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedUniversalToleranceNumerics
namespace SoficGroups.KunRootedUniversalToleranceNumerics
theorem _root_.solution
    {h d q t N b c e : ℝ}
    (hh : 0 < h) (hd : 0 < d) (hq : q < 1)
    (ht : 0 < t)
    (hbad : 2 * d * b ≤ t)
    (hmissing : N - 2 * b ≤ c)
    (hboundary : e ≤ 3 * t)
    (hslow :
      5 * (4 + h *
        (216 / (d * (1 - q) ^ 2) + 1 / d)) * t ≤ h * N) :
    e < (d * (1 - q) ^ 2 / 288) * c := by
  let δ : ℝ := d * (1 - q) ^ 2
  let γ : ℝ := δ / 288
  let C : ℝ := 216 / δ + 1 / d
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hγ : 0 < γ := by
    dsimp [γ]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hslowCscaled : h * (5 * C * t) ≤ h * N := by
    have hslow' : 5 * (4 + h * C) * t ≤ h * N := by
      simpa only [C, δ] using hslow
    nlinarith [mul_pos hh ht]
  have hslowC : 5 * C * t ≤ N :=
    le_of_mul_le_mul_left hslowCscaled hh
  have hb : 2 * b ≤ t / d := by
    apply (le_div_iff₀ hd).2
    nlinarith [hbad]
  have hgraph : N - t / d ≤ c := by
    linarith
  have hgraphscaled : γ * (N - t / d) ≤ γ * c :=
    mul_le_mul_of_nonneg_left hgraph hγ.le
  have hNscaled : γ * (5 * C * t) ≤ γ * N :=
    mul_le_mul_of_nonneg_left hslowC hγ.le
  have hγC : γ * C = (3 / 4 : ℝ) + γ / d := by
    change
      (δ / 288) * (216 / δ + 1 / d) =
        (3 / 4 : ℝ) + (δ / 288) / d
    field_simp [ne_of_gt hδ, ne_of_gt hd]
    ring
  have hidentity :
      γ * (5 * C * t) - γ * (t / d) =
        (15 / 4 : ℝ) * t + 4 * (γ / d) * t := by
    calc
      γ * (5 * C * t) - γ * (t / d) =
          5 * (γ * C) * t - (γ / d) * t := by ring
      _ = 5 * ((3 / 4 : ℝ) + γ / d) * t -
          (γ / d) * t := by rw [hγC]
      _ = (15 / 4 : ℝ) * t + 4 * (γ / d) * t := by ring
  have hpositive : 0 ≤ 4 * (γ / d) * t := by
    positivity
  have hstrict : 3 * t < γ * c := by
    nlinarith [hgraphscaled, hNscaled, hidentity]
  simpa only [γ, δ] using lt_of_le_of_lt hboundary hstrict
end SoficGroups.KunRootedUniversalToleranceNumerics

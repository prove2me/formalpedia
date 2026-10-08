-- Prove2me | solution 1 for RhinViola.normalizedLogLimitEventuallyBand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T16:56:17.76244+00:00
-- url     : https://prove2.me/submissions/6d8498e6-7cdc-4c06-a4b1-6ae3a2a846ad

import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open Filter

theorem solution
    (σ δ : ℝ) (g : ℕ → ℝ)
    (hδ : 0 < δ)
    (hlim : Tendsto g atTop (nhds (-σ))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      -(σ + δ) ≤ g n ∧ g n ≤ -(σ - δ) := by
  have hband :
      ∀ᶠ n : ℕ in atTop,
        -(σ + δ) ≤ g n ∧ g n ≤ -(σ - δ) := by
    have hlo :
        ∀ᶠ n : ℕ in atTop, -(σ + δ) < g n :=
      (tendsto_order.1 hlim).1 _ (by linarith)
    have hhi :
        ∀ᶠ n : ℕ in atTop, g n < -(σ - δ) :=
      (tendsto_order.1 hlim).2 _ (by linarith)
    filter_upwards [hlo, hhi] with n hnlo hnhi
    exact ⟨hnlo.le, hnhi.le⟩
  rcases Filter.eventually_atTop.1 hband with ⟨N, hN⟩
  exact ⟨N, hN⟩

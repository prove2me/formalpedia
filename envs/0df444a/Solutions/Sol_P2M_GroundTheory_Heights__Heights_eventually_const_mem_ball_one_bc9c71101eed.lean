-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eventually_const_mem_ball_one_bc9c71101eed
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T05:40:04.805634+00:00
-- url     : https://prove2.me/submissions/8e4d2be5-9185-44fe-bf6d-27afdebd4c8a

import Mathlib
open Filter Topology


theorem solution {r : ℝ} (hr : 0 < r) :
    ∀ᶠ τ in 𝓝 (0 : ℂ), (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r := by
  have h : Continuous (fun τ : ℂ => fun _ : Fin 1 => τ) := continuous_pi (fun _ => continuous_id)
  exact h.continuousAt (Metric.ball_mem_nhds (0 : Fin 1 → ℂ) hr)

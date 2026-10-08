-- Prove2me | solution 1 for RhinViola.normalizedLogLimitEventuallyNonzero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:32:32.063996+00:00
-- url     : https://prove2.me/submissions/356ad6aa-10ec-4d7b-a174-1094c26012db

import Mathlib

theorem solution
    (σ : ℝ) (f : ℕ → ℝ)
    (hσ : 0 < σ)
    (hlim : Filter.Tendsto
      (fun n : ℕ => Real.log |f n| / (n : ℝ))
      Filter.atTop (nhds (-σ))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n ≠ 0 := by
  have hneg : (-σ) < 0 := by linarith
  have hev : ∀ᶠ n : ℕ in Filter.atTop, Real.log |f n| / (n : ℝ) < 0 :=
    hlim.eventually (gt_mem_nhds hneg)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun n hn hf => ?_⟩
  have h := hN n hn
  rw [hf] at h
  simp at h


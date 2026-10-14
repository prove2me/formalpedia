-- Prove2me | solution 1 for Rudin.ch07_uniform_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-12T20:45:49.543709+00:00
-- url     : https://prove2.me/submissions/3892d135-385f-4352-87ad-e8f9c3dd9b19

import Mathlib

open Filter Topology

theorem solution {X : Type*} (E : Set X) (f : ℕ → X → ℂ) :
    (∃ g : X → ℂ, TendstoUniformlyOn f g atTop E) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ x ∈ E, ‖f n x - f m x‖ ≤ ε := by
  constructor
  · rintro ⟨g, hg⟩ ε hε
    have h := hg.uniformCauchySeqOn
    rw [Metric.uniformCauchySeqOn_iff] at h
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    have := hN m hm n hn x hx
    rw [dist_eq_norm] at this
    rw [norm_sub_rev]
    exact this.le
  · intro h
    have hU : UniformCauchySeqOn f atTop E := by
      rw [Metric.uniformCauchySeqOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
      refine ⟨N, fun m hm n hn x hx => ?_⟩
      rw [dist_eq_norm, norm_sub_rev]
      linarith [hN m hm n hn x hx]
    classical
    let g : X → ℂ := fun x => if x ∈ E then limUnder atTop (fun n => f n x) else 0
    refine ⟨g, hU.tendstoUniformlyOn_of_tendsto ?_⟩
    intro x hx
    have hc : CauchySeq (fun n => f n x) := hU.cauchySeq hx
    simp only [g, if_pos hx]
    exact hc.tendsto_limUnder

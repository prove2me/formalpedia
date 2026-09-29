-- Prove2me | solution 1 for Rudin.ch05_chain_rule
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T04:17:16.170607+00:00
-- url     : https://prove2.me/submissions/77637ffb-1ce1-4063-9af4-b6bcd34bbbed

import Mathlib

open Filter Topology

theorem solution (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
    DifferentiableAt ℝ (fun t => g (f t)) x ∧
      deriv (fun t => g (f t)) x = deriv g (f x) * deriv f x := by
  refine ⟨hg.comp x hf, ?_⟩
  exact deriv_comp x hg hf

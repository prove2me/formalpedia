-- Prove2me | solution 1 for Rudin.ch05_deriv_sum_product
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T04:16:49.814066+00:00
-- url     : https://prove2.me/submissions/9e8cdae1-b784-49fe-b3c5-d5b65c269831

import Mathlib

open Filter Topology

theorem solution (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun t => f t + g t) x ∧
      deriv (fun t => f t + g t) x = deriv f x + deriv g x ∧
    DifferentiableAt ℝ (fun t => f t * g t) x ∧
      deriv (fun t => f t * g t) x = deriv f x * g x + f x * deriv g x := by
  refine ⟨hf.add hg, deriv_add hf hg, hf.mul hg, ?_⟩
  exact (hf.hasDerivAt.mul hg.hasDerivAt).deriv

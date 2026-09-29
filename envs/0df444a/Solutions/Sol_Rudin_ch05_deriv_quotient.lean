-- Prove2me | solution 1 for Rudin.ch05_deriv_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T04:17:15.749167+00:00
-- url     : https://prove2.me/submissions/61bbe6ca-06b2-4e1d-85ad-aec37fd284e3

import Mathlib

open Filter Topology

theorem solution (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hgx : g x ≠ 0) :
    DifferentiableAt ℝ (fun t => f t / g t) x ∧
      deriv (fun t => f t / g t) x = (g x * deriv f x - deriv g x * f x) / (g x) ^ 2 := by
  refine ⟨hf.div hg hgx, ?_⟩
  have h : HasDerivAt (fun t => f t / g t)
      ((deriv f x * g x - f x * deriv g x) / (g x) ^ 2) x :=
    hf.hasDerivAt.div hg.hasDerivAt hgx
  rw [h.deriv]
  ring

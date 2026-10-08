-- Prove2me | solution 1 for WeightedRootIntegralIdentity.slitQuotientHolomorphicity
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T11:19:42.304475+00:00
-- url     : https://prove2.me/submissions/b3d9fa12-6b39-46e0-bf32-0afae153cb62

import Mathlib

theorem solution
    (G : ℂ → ℂ) (D : Set ℂ)
    (hG : DifferentiableOn ℂ G D)
    (hzero : ∀ z ∈ D, z ≠ 0) :
    DifferentiableOn ℂ (fun z => G z / z) D := by
  intro z hz
  exact (hG z hz).div (differentiableAt_id.differentiableWithinAt) (hzero z hz)

-- Prove2me | solution 1 for PHIP1887.central_jet_identity
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:21:54.522136+00:00
-- url     : https://prove2.me/submissions/110efd44-98f8-4a91-b527-13ea5b46137b

import Mathlib

theorem solution (y : ℂ) (k : ℕ) :
    (k : ℂ)^2 * (y*(1-y))^k * (1-2*y)^2
      - 2*(k : ℂ)*(y*(1-y))^(k+1)
    = (k : ℂ)^2 * (y*(1-y))^k
      - 2*(k : ℂ)*(2*(k : ℂ)+1)*(y*(1-y))^(k+1) := by
  simp only [pow_succ]
  ring

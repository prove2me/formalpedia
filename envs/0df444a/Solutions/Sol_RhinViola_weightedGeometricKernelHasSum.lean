-- Prove2me | solution 1 for RhinViola.weightedGeometricKernelHasSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T22:18:54.881103+00:00
-- url     : https://prove2.me/submissions/461ca074-d5bc-4851-b89c-3baee4b71931

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

theorem solution
    (h m : ℕ) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x * y < 1) :
    HasSum (fun k : ℕ => x ^ (h + k) * y ^ (m + k))
      (x ^ h * y ^ m / (1 - x * y)) := by
  have hgeo :=
    hasSum_geometric_of_lt_one (mul_nonneg hx hy) hxy
  have hscaled :=
    hgeo.mul_left (x ^ h * y ^ m)
  simpa [pow_add, mul_pow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled

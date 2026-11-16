-- Prove2me | solution 1 for PHIP1891.finite_branch_transfer
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:56:22.008764+00:00
-- url     : https://prove2.me/submissions/945dc5ad-ac17-4c90-afdc-df09c3c1bf17

import Mathlib
open MeasureTheory Set

theorem solution {X : Type*} (approx : ℕ → X)
    (value : X → ℝ) (v : ℝ) (finiteDefect : X → Prop)
    (finiteApprox : ∀ R, finiteDefect (approx R))
    (stableNegative : v < 0 → ∃ R, value (approx R) < 0)
    (branch2 : ∀ z, finiteDefect z → ¬ value z < 0) :
    0 ≤ v := by
  by_contra h
  have hv : v < 0 := lt_of_not_ge h
  obtain ⟨R, hR⟩ := stableNegative hv
  exact branch2 (approx R) (finiteApprox R) hR

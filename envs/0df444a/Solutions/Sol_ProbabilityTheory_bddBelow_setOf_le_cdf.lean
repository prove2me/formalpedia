-- Prove2me | solution 1 for ProbabilityTheory.bddBelow_setOf_le_cdf
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T00:31:23.208833+00:00
-- url     : https://prove2.me/submissions/6ba3ce0e-db51-4112-a003-03a948914a6f

import Mathlib

set_option autoImplicit false

-- carved verbatim out of submission 24af3a16-a50a-4c61-a8f1-d10c467ef9d4, lines 12-21


open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem solution (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u) :
    BddBelow {x | u ≤ cdf P x} := by
  have h := (tendsto_cdf_atBot P).eventually (gt_mem_nhds hu0)
  rw [Filter.eventually_atBot] at h
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx => ?_⟩
  by_contra hlt
  exact absurd (hx0 x (le_of_lt (not_le.mp hlt))) (not_lt.mpr hx)

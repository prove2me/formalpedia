-- Prove2me | solution 1 for ProbabilityTheory.nonempty_setOf_le_cdf
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T00:31:23.840123+00:00
-- url     : https://prove2.me/submissions/3ed84ed8-8f69-4a6d-b718-f4accca6c6e7

import Mathlib

set_option autoImplicit false

-- carved verbatim out of submission 24af3a16-a50a-4c61-a8f1-d10c467ef9d4, lines 22-27


open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem solution (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    ({x | u ≤ cdf P x} : Set ℝ).Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop P).eventually (lt_mem_nhds hu1)).exists
  exact ⟨x, hx.le⟩

-- Prove2me | solution 1 for SennottDP.Fatou.liminf_tsum_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:19:22.561262+00:00
-- url     : https://prove2.me/submissions/89f18b67-271b-4033-a1fc-8758d6ab5be7

import Mathlib

open Filter Topology
open scoped ENNReal

set_option autoImplicit false

open Filter Topology ENNReal in
theorem solution {S : Type*} [Countable S] (u : S → ℕ → ℝ≥0∞) :
    ∑' j, liminf (fun N => u j N) atTop ≤ liminf (fun N => ∑' j, u j N) atTop := by
  let _ : MeasurableSpace S := ⊤
  have h := MeasureTheory.lintegral_liminf_le (μ := MeasureTheory.Measure.count)
    (f := fun N j => u j N) (u := (atTop : Filter ℕ)) (fun _ => measurable_from_top)
  simpa [MeasureTheory.lintegral_count] using h

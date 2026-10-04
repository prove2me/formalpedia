-- Prove2me | solution 1 for SennottDP.Fatou.liminf_tsum_increasing_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:20:19.459154+00:00
-- url     : https://prove2.me/submissions/5884f2ce-e316-4d38-9d9e-5fdfece42581

import Mathlib

set_option autoImplicit false

open Filter Topology
open scoped ENNReal

open Filter Topology ENNReal in
theorem solution {S : Type*} [Countable S] (SN : ℕ → Set S)
    (hmono : Monotone SN) (hunion : ⋃ N, SN N = Set.univ) (u : S → ℕ → ℝ≥0∞) :
    ∑' j, liminf (fun N => u j N) atTop ≤
      liminf (fun N => ∑' j, (SN N).indicator (fun i => u i N) j) atTop := by
  let _ : MeasurableSpace S := ⊤
  have _ : MeasurableSingletonClass S := ⟨fun _ => trivial⟩
  have hev : ∀ j, liminf (fun N => u j N) atTop
      = liminf (fun N => (SN N).indicator (fun i => u i N) j) atTop := by
    intro j
    have hj : j ∈ ⋃ N, SN N := by rw [hunion]; trivial
    obtain ⟨N0, hN0⟩ := Set.mem_iUnion.mp hj
    apply Filter.liminf_congr
    filter_upwards [Filter.eventually_ge_atTop N0] with N hN
    rw [Set.indicator_of_mem (hmono hN hN0)]
  simp_rw [hev]
  have h := MeasureTheory.lintegral_liminf_le (μ := MeasureTheory.Measure.count) (u := atTop)
    (f := fun N j => (SN N).indicator (fun i => u i N) j) (fun _ => measurable_from_top)
  simpa only [MeasureTheory.lintegral_count] using h

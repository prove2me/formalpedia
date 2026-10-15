-- Prove2me | solution 1 for Plasticity.Topology.mem_intrinsicInterior_iff_ball
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:38:37.541922+00:00
-- url     : https://prove2.me/submissions/1c3d1382-58b2-42c0-8fb9-e39e9b1e2def

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Intrinsic

namespace Sol_Plasticity_Topology_mem_intrinsicInterior_iff_ball

end Sol_Plasticity_Topology_mem_intrinsicInterior_iff_ball

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (x : E) :
    x ∈ intrinsicInterior ℝ C ↔ ∃ ε > 0, ∀ w ∈ vectorSpan ℝ C, ‖w‖ < ε → x + w ∈ C := by
  by_cases hx : x ∉ C
  · -- both sides fail: `intrinsicInterior ℝ C ⊆ C`, and `w = 0` gives `x ∈ C`
    refine iff_of_false (fun h => hx (intrinsicInterior_subset h)) ?_
    rintro ⟨ε, hε, h⟩
    exact hx (by simpa using h 0 (Submodule.zero_mem _) (by simpa using hε))
  push_neg at hx
  have hxA : x ∈ affineSpan ℝ C := subset_affineSpan ℝ C hx
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy
    obtain ⟨ε, hε, hball⟩ := hy
    refine ⟨ε, hε, fun w hw hwε => ?_⟩
    have hmem : w +ᵥ (y : E) ∈ affineSpan ℝ C :=
      AffineSubspace.vadd_mem_of_mem_direction (by rwa [direction_affineSpan]) y.2
    have hin : (⟨w +ᵥ (y : E), hmem⟩ : affineSpan ℝ C) ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
      simpa [vadd_eq_add] using hwε
    have := hball hin
    simpa [vadd_eq_add, add_comm] using this
  · rintro ⟨ε, hε, h⟩
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    refine ⟨ε, hε, fun z hz => ?_⟩
    have hzx : (z : E) - x ∈ vectorSpan ℝ C := by
      rw [← direction_affineSpan]
      exact AffineSubspace.vsub_mem_direction z.2 hxA
    have hz' : ‖(z : E) - x‖ < ε := by
      rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] at hz
      simpa using hz
    have := h _ hzx hz'
    simpa using this

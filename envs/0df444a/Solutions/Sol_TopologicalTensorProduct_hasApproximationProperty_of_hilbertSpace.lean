-- Prove2me | solution 1 for TopologicalTensorProduct.hasApproximationProperty_of_hilbertSpace
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:27:57.183797+00:00
-- url     : https://prove2.me/submissions/6f7ac007-ee25-4d4d-bd8c-b102024db43b

import Mathlib
import Definitions.Def_TopologicalTensorProduct_ApproximationProperty

open Filter Topology
set_option autoImplicit false

open TopologicalTensorProduct

theorem solution (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    HasApproximationProperty ℂ H := by
  classical
  intro K hK U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨t, ht⟩ := hK (Metric.ball (0 : H) ε) (Metric.ball_mem_nhds 0 hε)
  let V : Submodule ℂ H := Submodule.span ℂ (t : Set H)
  have : FiniteDimensional ℂ V := FiniteDimensional.span_finset ℂ t
  let b := stdOrthonormalBasis ℂ V
  refine ⟨Module.finrank ℂ V, fun i => innerSL ℂ (b i : H), fun i => (b i : H), ?_⟩
  intro x hx
  have hsum : (∑ i, innerSL ℂ (b i : H) x • (b i : H)) = V.starProjection x := by
    rw [Submodule.starProjection_apply, b.orthogonalProjectionOnto_apply_eq_sum x]
    simp [innerSL_apply_apply]
  rw [hsum]
  apply hεU
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (ht hx)
  have hzV : z ∈ V := Submodule.subset_span (by exact_mod_cast hz)
  rw [Metric.mem_ball, dist_zero_right]
  have hmin : ‖x - V.starProjection x‖ ≤ ‖x - z‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨z, hzV⟩ : V)
  have hxz' : ‖x - z‖ < ε := by
    simpa [Metric.mem_ball, dist_zero_right] using hxz
  exact lt_of_le_of_lt hmin hxz'

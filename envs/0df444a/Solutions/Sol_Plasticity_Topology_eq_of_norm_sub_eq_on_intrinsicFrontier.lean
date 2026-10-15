-- Prove2me | solution 1 for Plasticity.Topology.eq_of_norm_sub_eq_on_intrinsicFrontier
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T02:25:07.394672+00:00
-- url     : https://prove2.me/submissions/7629f455-ef64-4ea2-a612-d666c2cd92bc

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Topology.Order.Monotone

namespace Sol_Plasticity_Topology_eq_of_norm_sub_eq_on_intrinsicFrontier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- From a point of the intrinsic interior one can step a little along any direction of the
vector span and stay in the set. -/
lemma exists_pos_add_smul_mem {C : Set E} {p v : E} (hp : p ∈ intrinsicInterior ℝ C)
    (hv : v ∈ vectorSpan ℝ C) : ∃ δ : ℝ, 0 < δ ∧ p + δ • v ∈ C := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hq
  obtain ⟨ε, hε, hball⟩ := hq
  have hpos : 0 < ‖v‖ + 1 := by positivity
  set δ : ℝ := ε / (2 * (‖v‖ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδv : ‖δ • v‖ < ε := by
    rw [norm_smul, Real.norm_of_nonneg hδpos.le, hδ, div_mul_eq_mul_div,
      div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  refine ⟨δ, hδpos, ?_⟩
  have hmem : δ • v +ᵥ (q : E) ∈ affineSpan ℝ C :=
    AffineSubspace.vadd_mem_of_mem_direction
      (by rw [direction_affineSpan]; exact Submodule.smul_mem _ _ hv) q.2
  have hin : (⟨δ • v +ᵥ (q : E), hmem⟩ : affineSpan ℝ C) ∈ Metric.ball q ε := by
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
    simpa [vadd_eq_add] using hδv
  have := hball hin
  simpa [vadd_eq_add, add_comm] using this

/-- The exit point `x + s • v`, `s = sup {t | x + t • v ∈ C}`, of the ray from `x ∈ C` in a
direction `v ≠ 0` of the vector span of a bounded set `C` lies in the intrinsic frontier and in
the closure of `C`, and `s` bounds every parameter of a point of `C` on the ray. -/
lemma exists_exit_point {C : Set E} (hC : Bornology.IsBounded C) {x v : E} (hx : x ∈ C)
    (hv : v ∈ vectorSpan ℝ C) (hv0 : v ≠ 0) :
    ∃ s : ℝ, (∀ t : ℝ, x + t • v ∈ C → t ≤ s) ∧ x + s • v ∈ intrinsicFrontier ℝ C ∧
      x + s • v ∈ closure C := by
  set S : Set ℝ := {t | x + t • v ∈ C} with hS
  have hSne : S.Nonempty := ⟨0, by simpa [hS] using hx⟩
  obtain ⟨R, hR⟩ := hC.exists_norm_le
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hSbdd : BddAbove S := by
    refine ⟨2 * R / ‖v‖, fun t ht => ?_⟩
    rw [le_div_iff₀ hvpos]
    have h1 : ‖x + t • v‖ ≤ R := hR _ ht
    have h2 : ‖x‖ ≤ R := hR _ hx
    have h3 : t * ‖v‖ ≤ ‖t • v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (le_abs_self t) (norm_nonneg v)
    have h4 : ‖t • v‖ ≤ ‖x + t • v‖ + ‖x‖ := by
      calc ‖t • v‖ = ‖(x + t • v) - x‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖x + t • v‖ + ‖x‖ := norm_sub_le _ _
    linarith
  have hle : ∀ t : ℝ, x + t • v ∈ C → t ≤ sSup S := fun t ht => le_csSup hSbdd ht
  have hcont : Continuous fun t : ℝ => x + t • v := by fun_prop
  have hcl : x + sSup S • v ∈ closure C :=
    map_mem_closure (f := fun t : ℝ => x + t • v) hcont (csSup_mem_closure hSne hSbdd) (fun t ht => ht)
  have hspan : x + sSup S • v ∈ affineSpan ℝ C := by
    have := AffineSubspace.vadd_mem_of_mem_direction
      (by rw [direction_affineSpan]; exact Submodule.smul_mem _ (sSup S) hv)
      (subset_affineSpan ℝ C hx)
    rwa [vadd_eq_add, add_comm] at this
  have hicl : x + sSup S • v ∈ intrinsicClosure ℝ C := by
    rw [intrinsicClosure_eq_closure_inter_affineSpan]
    exact ⟨hcl, hspan⟩
  have hnint : x + sSup S • v ∉ intrinsicInterior ℝ C := by
    intro hint
    obtain ⟨δ, hδ, hmem⟩ := exists_pos_add_smul_mem hint hv
    have : sSup S + δ ≤ sSup S := hle _ (by rwa [add_smul, ← add_assoc])
    linarith
  refine ⟨sSup S, hle, ?_, hcl⟩
  rw [← intrinsicClosure_sdiff_intrinsicInterior]
  exact ⟨hicl, hnint⟩

end Sol_Plasticity_Topology_eq_of_norm_sub_eq_on_intrinsicFrontier

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : Bornology.IsBounded C) (x y : E) (hx : x ∈ C) (hy : y ∈ C)
    (h : ∀ b ∈ intrinsicFrontier ℝ C, ‖x - b‖ = ‖y - b‖) :
    x = y := by
  by_contra hxy
  have hv0 : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  have hv : y - x ∈ vectorSpan ℝ C := by
    simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ hy hx
  obtain ⟨s, hle, hfr, -⟩ :=
    Sol_Plasticity_Topology_eq_of_norm_sub_eq_on_intrinsicFrontier.exists_exit_point hC hx hv hv0
  have hs1 : 1 ≤ s := hle 1 (by simpa using hy)
  have heq := h _ hfr
  have e1 : x - (x + s • (y - x)) = -(s • (y - x)) := by abel
  have e2 : y - (x + s • (y - x)) = (1 - s) • (y - x) := by
    rw [sub_smul, one_smul]; abel
  rw [e1, e2, norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ s),
    Real.norm_eq_abs, abs_of_nonpos (by linarith : 1 - s ≤ 0)] at heq
  have hvpos : 0 < ‖y - x‖ := norm_pos_iff.2 hv0
  nlinarith

-- Prove2me | solution 1 for Plasticity.Topology.norm_map_sub_map_eq_of_intrinsicFrontier
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T02:25:38.888003+00:00
-- url     : https://prove2.me/submissions/99145036-d8a8-4f8d-82ab-083038dc048e

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Monotone

namespace Sol_Plasticity_Topology_norm_map_sub_map_eq_of_intrinsicFrontier

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

end Sol_Plasticity_Topology_norm_map_sub_map_eq_of_intrinsicFrontier

theorem solution {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] (D : Set E) (hclosed : IsClosed D) (hbdd : Bornology.IsBounded D)
    (f : E → E') (hlip : LipschitzOnWith 1 f D)
    (hfr : ∀ b ∈ intrinsicFrontier ℝ D, ∀ b' ∈ intrinsicFrontier ℝ D, ‖f b - f b'‖ = ‖b - b'‖) :
    ∀ x ∈ D, ∀ x' ∈ D, ‖f x - f x'‖ = ‖x - x'‖ := by
  have hL : ∀ a ∈ D, ∀ b ∈ D, ‖f a - f b‖ ≤ ‖a - b‖ := by
    intro a ha b hb
    simpa [dist_eq_norm] using hlip.dist_le_mul a ha b hb
  intro x hx x' hx'
  by_cases hxx : x = x'
  · subst hxx; simp
  obtain ⟨v, rfl⟩ : ∃ v, x' = x + v := ⟨x' - x, by abel⟩
  have hv0 : v ≠ 0 := fun h => hxx (by rw [h, add_zero])
  have hv : v ∈ vectorSpan ℝ D := by
    simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ hx' hx
  -- the exit points of the line through `x` and `x + v`, beyond `x + v` and behind `x`
  obtain ⟨s, hle, hfr1, hcl1⟩ := Sol_Plasticity_Topology_norm_map_sub_map_eq_of_intrinsicFrontier.exists_exit_point hbdd hx hv hv0
  obtain ⟨t, hle', hfr2, hcl2⟩ :=
    Sol_Plasticity_Topology_norm_map_sub_map_eq_of_intrinsicFrontier.exists_exit_point hbdd hx (neg_mem hv) (neg_ne_zero.2 hv0)
  have hs1 : 1 ≤ s := hle 1 (by simpa using hx')
  have ht0 : 0 ≤ t := hle' 0 (by simpa using hx)
  rw [hclosed.closure_eq] at hcl1 hcl2
  have hpp := hfr _ hfr2 _ hfr1
  have h1 := hL _ hcl2 x hx
  have h2 := hL _ hx' _ hcl1
  have tri : ‖f (x + t • -v) - f (x + s • v)‖ ≤ ‖f (x + t • -v) - f x‖ + ‖f x - f (x + v)‖
      + ‖f (x + v) - f (x + s • v)‖ := by
    calc ‖f (x + t • -v) - f (x + s • v)‖
        ≤ ‖f (x + t • -v) - f x‖ + ‖f x - f (x + s • v)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖f (x + t • -v) - f x‖ + (‖f x - f (x + v)‖ + ‖f (x + v) - f (x + s • v)‖) := by
          gcongr; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = _ := by ring
  have n1 : ‖(x + t • -v) - (x + s • v)‖ = (t + s) * ‖v‖ := by
    have : (x + t • -v) - (x + s • v) = -((t + s) • v) := by rw [smul_neg, add_smul]; abel
    rw [this, norm_neg, norm_smul, Real.norm_of_nonneg (by linarith)]
  have n2 : ‖(x + t • -v) - x‖ = t * ‖v‖ := by
    rw [add_sub_cancel_left, norm_smul, norm_neg, Real.norm_of_nonneg ht0]
  have n3 : ‖(x + v) - (x + s • v)‖ = (s - 1) * ‖v‖ := by
    have : (x + v) - (x + s • v) = -((s - 1) • v) := by rw [sub_smul, one_smul]; abel
    rw [this, norm_neg, norm_smul, Real.norm_of_nonneg (by linarith)]
  have n4 : ‖x - (x + v)‖ = ‖v‖ := by rw [sub_add_cancel_left, norm_neg]
  have h3 := hL x hx _ hx'
  rw [n1] at hpp
  rw [n2] at h1
  rw [n3] at h2
  rw [n4] at h3 ⊢
  linarith

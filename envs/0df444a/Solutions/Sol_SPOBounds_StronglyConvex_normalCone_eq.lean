-- Prove2me | solution 1 for SPOBounds.StronglyConvex.normalCone_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:18:15.011975+00:00
-- url     : https://prove2.me/submissions/51e8649c-52d1-4273-8a73-20280a12084f

import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_StronglyConvex_StronglyConvexSet

namespace SPOBounds.StronglyConvex

/-- In finite dimension, the dual norm of a functional is attained on the closed unit ball. -/
theorem aux_nce_norming {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (c : StrongDual ℝ E) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ c x = ‖c‖ := by
  have hK : IsCompact ((fun x => ‖c x‖) '' Metric.closedBall (0 : E) 1) :=
    (isCompact_closedBall (0 : E) 1).image (by fun_prop)
  have hne : ((fun x => ‖c x‖) '' Metric.closedBall (0 : E) 1).Nonempty :=
    (Metric.nonempty_closedBall.mpr zero_le_one).image _
  have hmem := hK.sSup_mem hne
  rw [ContinuousLinearMap.sSup_unitClosedBall_eq_norm] at hmem
  obtain ⟨x, hx, hxc⟩ := hmem
  rw [mem_closedBall_zero_iff] at hx
  simp only [Real.norm_eq_abs] at hxc
  rcases abs_cases (c x) with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact ⟨x, hx, by linarith⟩
  · refine ⟨-x, by rwa [norm_neg], ?_⟩
    rw [map_neg]
    linarith

theorem aux_nce_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {μbar : ℝ} (hμ : 0 ≤ μbar) {S : Set E}
    (hSsc : StronglyConvexSet μbar S) {wbar : E} (hwbar : wbar ∈ S)
    (c : StrongDual ℝ E) (hc : c ∈ normalCone S wbar) (v : E) (hv : v ∈ S) :
    c (v - wbar) ≤ -(μbar / 2) * ‖c‖ * ‖v - wbar‖ ^ 2 := by
  simp only [normalCone, Set.mem_setOf_eq] at hc
  obtain ⟨x, hx, hcx⟩ := aux_nce_norming c
  have key : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      c (v - wbar) ≤ -(μbar / 2) * ‖c‖ * ‖v - wbar‖ ^ 2 * (1 - t) := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h1t : 0 ≤ 1 - t := by linarith
    set r := (μbar / 2) * t * (1 - t) * ‖v - wbar‖ ^ 2 with hr
    have hr0 : 0 ≤ r := by positivity
    have hp : t • v + (1 - t) • wbar + r • x ∈ S := by
      apply hSsc.2 v hv wbar hwbar t ⟨ht0.le, ht1.le⟩
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hr0]
      calc r * ‖x‖ ≤ r * 1 := by gcongr
        _ = _ := by rw [mul_one]
    have h1 := hc _ hp
    have heq : t • v + (1 - t) • wbar + r • x - wbar = t • (v - wbar) + r • x := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [heq, map_add, map_smul, map_smul, hcx, smul_eq_mul, smul_eq_mul] at h1
    have h2 : t * c (v - wbar) ≤ t * (-(μbar / 2) * ‖c‖ * ‖v - wbar‖ ^ 2 * (1 - t)) := by
      rw [hr] at h1
      linarith
    exact le_of_mul_le_mul_left h2 ht0
  have htend : Filter.Tendsto (fun t : ℝ => -(μbar / 2) * ‖c‖ * ‖v - wbar‖ ^ 2 * (1 - t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(μbar / 2) * ‖c‖ * ‖v - wbar‖ ^ 2)) := by
    have hcont : Continuous (fun t : ℝ => -(μbar / 2) * ‖c‖ * ‖v - wbar‖ ^ 2 * (1 - t)) := by
      fun_prop
    have h2 := hcont.tendsto 0
    simp only [sub_zero, mul_one] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  exact key t ht

end SPOBounds.StronglyConvex

open SPOBounds.StronglyConvex

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {μbar : ℝ} (hμ : 0 ≤ μbar) {S : Set E}
    (hSsc : StronglyConvexSet μbar S) {wbar : E} (hwbar : wbar ∈ S) :
    normalCone S wbar =
      {c : StrongDual ℝ E | ∀ v ∈ S, c (v - wbar) ≤ -(μbar / 2) * ‖c‖ * ‖v - wbar‖ ^ 2} := by
  ext c
  constructor
  · intro hc v hv
    exact aux_nce_sub hμ hSsc hwbar c hc v hv
  · intro hc
    simp only [Set.mem_setOf_eq] at hc
    simp only [normalCone, Set.mem_setOf_eq]
    intro v hv
    have h1 := hc v hv
    have h2 : 0 ≤ (μbar / 2) * ‖c‖ * ‖v - wbar‖ ^ 2 := by positivity
    linarith

-- Prove2me | solution 1 for ProcessingNetworks.ProportionalFairness.within_group_entropy_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:27:12.579164+00:00
-- url     : https://prove2.me/submissions/a1e248b9-7dbb-4884-9c6d-0fc4c0916ab3

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_WithinGroupEntropy

namespace WGE705

/-- `z * log Y` is continuous on `S` when `0 ≤ z ≤ Y` there. -/
theorem mul_log_cont {S : Set ℝ} {z Y : ℝ → ℝ} (hz : ContinuousOn z S) (hY : ContinuousOn Y S)
    (h0 : ∀ t ∈ S, 0 ≤ z t) (h1 : ∀ t ∈ S, z t ≤ Y t) :
    ContinuousOn (fun t => z t * Real.log (Y t)) S := by
  intro t0 ht0
  by_cases hY0 : Y t0 = 0
  · have hz0 : z t0 = 0 := le_antisymm (hY0 ▸ h1 t0 ht0) (h0 t0 ht0)
    show Filter.Tendsto (fun t => z t * Real.log (Y t)) (nhdsWithin t0 S)
      (nhds (z t0 * Real.log (Y t0)))
    rw [hz0, zero_mul]
    have hYlog : Filter.Tendsto (fun t => Y t * Real.log (Y t)) (nhdsWithin t0 S) (nhds 0) := by
      have := (Real.continuous_mul_log.continuousAt (x := Y t0)).tendsto.comp (hY t0 ht0)
      simpa [Function.comp_def, hY0] using this
    have h2 : Filter.Tendsto (fun t => ‖Y t * Real.log (Y t)‖) (nhdsWithin t0 S) (nhds 0) := by
      simpa using hYlog.norm
    refine squeeze_zero_norm' ?_ h2
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h0 t ht)]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((h0 t ht).trans (h1 t ht))]
      exact mul_le_mul_of_nonneg_right (h1 t ht) (abs_nonneg _)
  · exact (hz t0 ht0).mul ((hY t0 ht0).log hY0)

end WGE705

open ProcessingNetworks.ProportionalFairness in
theorem solution
    {I L : ℕ} (grp : Fin I → Fin L) (Zh : ℝ → Fin I → ℝ)
    (hZcont : ContinuousOn Zh (Set.Ici 0)) (hZnn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ Zh t i) :
    ContinuousOn (withinGroupEntropy grp Zh) (Set.Ici 0) := by
  have hc : ∀ i, ContinuousOn (fun t => Zh t i) (Set.Ici 0) := fun i =>
    (continuous_apply i).comp_continuousOn hZcont
  have hYc : ∀ i, ContinuousOn (fun t => groupAggregate grp (Zh t) (grp i)) (Set.Ici 0) := by
    intro i
    unfold groupAggregate
    exact continuousOn_finsetSum _ (fun j _ => hc j)
  have hle : ∀ i, ∀ t ∈ Set.Ici (0:ℝ), Zh t i ≤ groupAggregate grp (Zh t) (grp i) := by
    intro i t ht
    unfold groupAggregate
    exact Finset.single_le_sum (f := fun j => Zh t j)
      (fun j _ => hZnn t ht j) (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
  have key : ContinuousOn (fun t => ∑ i, (Zh t i * Real.log (Zh t i)
      - Zh t i * Real.log (groupAggregate grp (Zh t) (grp i)))) (Set.Ici 0) := by
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    refine ContinuousOn.sub ?_ ?_
    · exact Real.continuous_mul_log.comp_continuousOn (hc i)
    · exact WGE705.mul_log_cont (hc i) (hYc i) (fun t ht => hZnn t ht i) (hle i)
  refine key.congr ?_
  intro t ht
  unfold withinGroupEntropy
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : Zh t i = 0
  · simp [h]
  · rw [if_neg h]
    have hpos : 0 < Zh t i := lt_of_le_of_ne (hZnn t ht i) (Ne.symm h)
    have hYpos : 0 < groupAggregate grp (Zh t) (grp i) := hpos.trans_le (hle i t ht)
    rw [Real.log_div h hYpos.ne', mul_sub]

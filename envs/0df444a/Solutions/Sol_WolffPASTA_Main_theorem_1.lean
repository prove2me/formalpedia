-- Prove2me | solution 1 for WolffPASTA.Main.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:06:05.318265+00:00
-- url     : https://prove2.me/submissions/cb6bbf7d-9c3e-4a69-a0d6-4e90a6aac522

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting
import Theorems.Thm_WolffPASTA_Main_lemma_2
import Theorems.Thm_WolffPASTA_Main_arrival_rate_limit

open MeasureTheory ProbabilityTheory Filter Topology
open WolffPASTA.Main

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Type*} [MeasurableSpace S] (N : ℝ → Ω → S)
    (A : ℝ → Ω → ℕ) (lam : ℝ) (hlam : 0 < lam) (hA : IsPoissonProcess P A lam)
    (B : Set S) (hB : ∀ t, 0 ≤ t → MeasurableSet {ω | N t ω ∈ B})
    (hpath : PathRegular P (U N B))
    (hjoint : JointlyMeasurable (U N B))
    (hLAA : LAAJoint P A (U N B))
    (Vinf : Ω → ℝ) :
    (∀ᵐ ω ∂P, Tendsto (fun t => V (U N B) t ω) atTop (𝓝 (Vinf ω))) ↔
      (∀ᵐ ω ∂P, Tendsto (fun t => Z (U N B) A t ω) atTop (𝓝 (Vinf ω))) := by
  have h2 := lemma_2 P N A lam hlam hA B hB hpath hjoint hLAA
  have h3 := arrival_rate_limit P A lam hlam hA
  -- pointwise identity: R/t = Y/t - lam * V for t ≠ 0
  have hR : ∀ ω t, t ≠ 0 → R (U N B) A lam t ω / t
      = Y (U N B) A t ω / t - lam * V (U N B) t ω := by
    intro ω t ht
    simp only [R]
    field_simp
  -- eventually A t ω > 0
  have hpos : ∀ ω, Tendsto (fun t => (A t ω : ℝ) / t) atTop (𝓝 lam) →
      ∀ᶠ t in atTop, 0 < (A t ω : ℝ) / t ∧ 0 < t := by
    intro ω hω
    exact (hω.eventually (lt_mem_nhds hlam)).and (eventually_gt_atTop 0)
  constructor
  · intro hV
    filter_upwards [hV, h2, h3] with ω hVω h2ω h3ω
    -- Y/t → lam * Vinf
    have hY : Tendsto (fun t => Y (U N B) A t ω / t) atTop (𝓝 (lam * Vinf ω)) := by
      have := h2ω.add (hVω.const_mul lam)
      rw [zero_add] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [hR ω t ht.ne']
      ring
    have hq := hY.div h3ω hlam.ne'
    rw [mul_div_cancel_left₀ _ hlam.ne'] at hq
    refine hq.congr' ?_
    filter_upwards [hpos ω h3ω] with t ⟨hAt, ht⟩
    have hA0 : (A t ω : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_div] at hAt; exact lt_irrefl _ hAt
    simp only [Z, Pi.div_apply]
    field_simp
  · intro hZ
    filter_upwards [hZ, h2, h3] with ω hZω h2ω h3ω
    have hY : Tendsto (fun t => Y (U N B) A t ω / t) atTop (𝓝 (Vinf ω * lam)) := by
      refine (hZω.mul h3ω).congr' ?_
      filter_upwards [hpos ω h3ω] with t ⟨hAt, ht⟩
      have hA0 : (A t ω : ℝ) ≠ 0 := by
        intro h0; rw [h0, zero_div] at hAt; exact lt_irrefl _ hAt
      simp only [Z]
      field_simp
    have hlV : Tendsto (fun t => lam * V (U N B) t ω) atTop (𝓝 (Vinf ω * lam)) := by
      have := hY.sub h2ω
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [hR ω t ht.ne']
      ring
    have := hlV.const_mul lam⁻¹
    rw [show lam⁻¹ * (Vinf ω * lam) = Vinf ω by field_simp] at this
    refine this.congr' (Eventually.of_forall fun t => ?_)
    field_simp

-- Prove2me | solution 1 for RapidRatePoisson.WeakConv.scaledComp_tendsto
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-31T10:54:42.803586+00:00
-- url     : https://prove2.me/submissions/364d7b0a-ff8d-41cb-94c1-cd58560fc61c

import Mathlib
import Definitions.Def_RapidRatePoisson_WeakConv_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open RapidRatePoisson.WeakConv



theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : ℝ≥0 → Ω → ℝ) (lamStar : ℝ≥0)
    (_hA1 : Assumption1 P A lamStar) (t : ℝ≥0),
    TendstoInMeasure P (fun (ε : ℝ≥0) ω => scaledComp A ε t ω) (𝓝[>] 0)
      (fun _ => (lamStar : ℝ) * t)) := by
  intro H
  -- the trivial σ-algebra on `ULift ℕ`
  let mΩ : MeasurableSpace (ULift.{0} ℕ) := ⊥
  let P : Measure (ULift.{0} ℕ) := Measure.dirac ⟨0⟩
  haveI : IsProbabilityMeasure P := by
    constructor
    simp [P, Measure.dirac_apply_of_mem (Set.mem_univ _)]
  -- every nonempty set has outer measure one
  have hfull : ∀ s : Set (ULift.{0} ℕ), s.Nonempty → P s = 1 := by
    intro s hs
    have hm : MeasurableSet[mΩ] (toMeasurable P s) := measurableSet_toMeasurable P s
    have hsub : s ⊆ toMeasurable P s := subset_toMeasurable P s
    rcases MeasurableSpace.measurableSet_bot_iff.mp hm with h | h
    · obtain ⟨x, hx⟩ := hs
      have := hsub hx
      rw [h] at this
      exact absurd this (Set.notMem_empty x)
    · rw [← measure_toMeasurable, h]
      exact measure_univ
  let A : ℝ≥0 → ULift.{0} ℕ → ℝ := fun t ω => if t = 0 then (ω.down : ℝ) else (t : ℝ)
  have hA1 : Assumption1 P A 1 := by
    refine ⟨one_pos, ?_⟩
    intro δ hδ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ≥0)] with t ht
    have ht0 : t ≠ 0 := by
      intro h; rw [h] at ht; exact absurd ht (by norm_num)
    have htr : (t : ℝ) ≠ 0 := by exact_mod_cast ht0
    have : {x : ULift.{0} ℕ | δ ≤ edist (A t x / (t : ℝ)) ((1 : ℝ≥0) : ℝ)} = ∅ := by
      ext x
      simp only [A, if_neg ht0, div_self htr, NNReal.coe_one, edist_self, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_le]
      exact hδ
    rw [this, measure_empty]
  have h0 := H P A 1 hA1 0 1 one_pos
  -- the sets in question are all nonempty, so have measure one
  have hone : ∀ ε : ℝ≥0, 0 < ε →
      P {x | (1 : ℝ≥0∞) ≤ edist (scaledComp A ε 0 x) (((1 : ℝ≥0) : ℝ) * ((0 : ℝ≥0) : ℝ))} = 1 := by
    intro ε hε
    apply hfull
    refine ⟨⟨⌈(1 : ℝ) / ε⌉₊⟩, ?_⟩
    simp only [Set.mem_setOf_eq, scaledComp, A, zero_div, if_true, NNReal.coe_zero, mul_zero]
    rw [edist_dist, Real.dist_eq, sub_zero]
    have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
    have h1 : (1 : ℝ) / ε ≤ (⌈(1 : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (1 : ℝ) ≤ (ε : ℝ) * (⌈(1 : ℝ) / ε⌉₊ : ℝ) := by
      rw [div_le_iff₀ hεr] at h1; linarith
    have h3 : (1 : ℝ) ≤ |(ε : ℝ) * (⌈(1 : ℝ) / ε⌉₊ : ℝ)| := le_trans h2 (le_abs_self _)
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal h3
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      P {x | (1 : ℝ≥0∞) ≤ edist (scaledComp A ε 0 x) (((1 : ℝ≥0) : ℝ) * ((0 : ℝ≥0) : ℝ))} = 1 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε using hone ε hε
  have hlim := tendsto_nhds_unique (h0.congr' (hev.mono fun _ h => h)) tendsto_const_nhds
  · exact absurd hlim (by norm_num)

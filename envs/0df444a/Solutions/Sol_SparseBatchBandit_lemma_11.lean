-- Prove2me | solution 1 for SparseBatchBandit.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:44:26.028345+00:00
-- url     : https://prove2.me/submissions/aa0739b5-7003-4769-9e4e-53a2760a860b

import Mathlib
import Definitions.Def_SparseBatchBandit_maxArm
open MeasureTheory ProbabilityTheory
open scoped NNReal

open SparseBatchBandit in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K : ℕ} [NeZero K] (X : Fin K → Ω → ℝ) (σ : ℝ≥0) (_hσ : 0 < σ)
    (_hX : ∀ k, HasSubgaussianMGF (X k) (σ ^ 2) P) (t : ℝ) (_ht : 0 < t) :
    P.real {ω | t ≤ maxArm (fun k => X k ω)} ≤
      (K : ℝ) * Real.exp (-t ^ 2 / (2 * (σ : ℝ) ^ 2)) := by
  have hsub : {ω | t ≤ maxArm (fun k => X k ω)} ⊆ ⋃ k, {ω | t ≤ X k ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, maxArm, Finset.le_sup'_iff] at hω
    obtain ⟨k, _, hk⟩ := hω
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  calc P.real {ω | t ≤ maxArm (fun k => X k ω)}
      ≤ P.real (⋃ k, {ω | t ≤ X k ω}) := measureReal_mono hsub
    _ ≤ ∑ k, P.real {ω | t ≤ X k ω} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin K, Real.exp (-t ^ 2 / (2 * (σ : ℝ) ^ 2)) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have := (_hX k).measure_ge_le _ht.le
        simpa [NNReal.coe_pow] using this
    _ = (K : ℝ) * Real.exp (-t ^ 2 / (2 * (σ : ℝ) ^ 2)) := by
        simp

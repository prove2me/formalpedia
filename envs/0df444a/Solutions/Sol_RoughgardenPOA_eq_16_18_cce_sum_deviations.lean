-- Prove2me | solution 1 for RoughgardenPOA.eq_16_18_cce_sum_deviations
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:10:16.202062+00:00
-- url     : https://prove2.me/submissions/0956cf9a-4fd5-473c-9f4c-6b8ddef9a630

import Mathlib
import Definitions.Def_RoughgardenPOA_objective
import Definitions.Def_RoughgardenPOA_IsCCE

open RoughgardenPOA in
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (C : ι → (∀ i, S i) → ℝ) (σ : MeasureTheory.Measure (∀ i, S i)) (hσ : IsCCE C σ)
    (sStar : ∀ i, S i) :
    ∫ s, objective C s ∂σ ≤ ∑ i, ∫ s, C i (Function.update s i (sStar i)) ∂σ := by
  obtain ⟨_, hint, _, hdev⟩ := hσ
  have h : ∫ s, objective C s ∂σ = ∑ i, ∫ s, C i s ∂σ := by
    unfold objective
    exact MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hint i)
  rw [h]
  exact Finset.sum_le_sum (fun i _ => hdev i (sStar i))

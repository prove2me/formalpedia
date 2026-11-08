-- Prove2me | solution 1 for SuperPareto.step_d_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:14:03.684094+00:00
-- url     : https://prove2.me/submissions/0808f6e4-1b01-4e0a-848c-406d1f03fb9e

import Mathlib

open MeasureTheory

theorem solution {Ω ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (A : ι → Set Ω)
    (θ : ι → ℝ) (ω : Ω) :
    ∑ i, θ i * (A i).indicator (X i) ω =
      ∑ S : Finset ι, ((⋂ i ∈ S, A i) ∩ (⋂ (i) (_ : i ∉ S), (A i)ᶜ)).indicator
        (fun ω' => ∑ i ∈ S, θ i * X i ω') ω := by
  classical
  obtain ⟨S0, hS0⟩ : ∃ S0 : Finset ι, S0 = Finset.univ.filter (fun i => ω ∈ A i) := ⟨_, rfl⟩
  have hmem0 : ∀ i, i ∈ S0 ↔ ω ∈ A i := by
    intro i; rw [hS0]; simp
  rw [Finset.sum_eq_single S0]
  · rw [Set.indicator_of_mem]
    · rw [hS0, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : ω ∈ A i
      · rw [Set.indicator_of_mem h, if_pos h]
      · rw [Set.indicator_of_notMem h, if_neg h, mul_zero]
    · simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
      exact ⟨fun i hi => (hmem0 i).mp hi, fun i hi h => hi ((hmem0 i).mpr h)⟩
  · intro S _ hS
    apply Set.indicator_of_notMem
    intro hmem
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff] at hmem
    obtain ⟨h1, h2⟩ := hmem
    apply hS
    ext i
    rw [hmem0]
    constructor
    · exact h1 i
    · intro hi
      by_contra hn
      exact h2 i hn hi
  · intro h
    exact absurd (Finset.mem_univ _) h

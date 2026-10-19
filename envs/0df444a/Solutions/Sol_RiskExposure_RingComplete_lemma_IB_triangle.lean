-- Prove2me | solution 1 for RiskExposure.RingComplete.lemma_IB_triangle
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:35:41.759856+00:00
-- url     : https://prove2.me/submissions/69e012be-2f5a-47ca-8a7e-11438d41c05f

import Mathlib
set_option autoImplicit false

theorem solution {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (A : ι → ℝ) (B : ℝ)
    (hB : B < s.sup' hs A) :
    max (∑ i ∈ s, A i - B) 0 + B ≤ ∑ i ∈ s, max (A i) 0 := by
  obtain ⟨i0, hi0, heq⟩ := Finset.exists_mem_eq_sup' hs A
  rw [heq] at hB
  have h1 : ∑ i ∈ s, A i ≤ ∑ i ∈ s, max (A i) 0 :=
    Finset.sum_le_sum fun i _ => le_max_left _ _
  have h2 : max (A i0) 0 ≤ ∑ i ∈ s, max (A i) 0 :=
    Finset.single_le_sum (f := fun i => max (A i) 0) (fun i _ => le_max_right _ _) hi0
  rcases le_total 0 (∑ i ∈ s, A i - B) with h | h
  · rw [max_eq_left h]; linarith
  · rw [max_eq_right h]; have := le_max_left (A i0) 0; linarith

-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_mem_of_bounded_nat_set
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:31:25.686057+00:00
-- url     : https://prove2.me/submissions/6093dc50-2970-4b57-93a2-21f2a689b55f

import Mathlib

set_option autoImplicit false

theorem solution
    (S : Set Nat) (B : Nat) (hS : S.Nonempty)
    (hB : ∀ n ∈ S, n ≤ B) :
    ∃ m ∈ S, ∀ n ∈ S, n ≤ m := by
  classical
  let T : Finset Nat := (Finset.range (B + 1)).filter (fun n => n ∈ S)
  have hT : T.Nonempty := by
    obtain ⟨a, ha⟩ := hS
    refine ⟨a, ?_⟩
    change a ∈ (Finset.range (B + 1)).filter (fun n => n ∈ S)
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      have haB := hB a ha
      omega
    · exact ha
  let m : Nat := T.max' hT
  have hmT : m ∈ T := by
    simpa [m] using T.max'_mem hT
  refine ⟨m, ?_, ?_⟩
  · have hmFilter : m ∈ (Finset.range (B + 1)).filter (fun n => n ∈ S) := by
      simpa [T] using hmT
    exact (Finset.mem_filter.mp hmFilter).2
  · intro n hn
    have hnT : n ∈ T := by
      change n ∈ (Finset.range (B + 1)).filter (fun n => n ∈ S)
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        have hnB := hB n hn
        omega
      · exact hn
    change n ≤ T.max' hT
    exact T.le_max' n hnT
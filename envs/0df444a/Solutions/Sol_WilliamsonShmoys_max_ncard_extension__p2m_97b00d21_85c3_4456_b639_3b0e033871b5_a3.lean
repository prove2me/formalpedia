-- Prove2me | solution 1 for WilliamsonShmoys.max_ncard_extension__p2m_97b00d21_85c3_4456_b639_3b0e033871b5_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:39:40.710627+00:00
-- url     : https://prove2.me/submissions/4d2d53b9-47ce-4b52-a545-05d3abafefd0

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop) (hP : ∃ G, P G) :
    ∃ L, P L ∧ ∀ M, P M → M.edgeSet.ncard ≤ L.edgeSet.ncard := by
  classical
  obtain ⟨G, hG⟩ := hP
  let N : ℕ := Fintype.card (Sym2 V)
  have hbound (H : SimpleGraph V) : H.edgeSet.ncard ≤ N := by
    dsimp [N]
    calc
      H.edgeSet.ncard ≤ (Set.univ : Set (Sym2 V)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
      _ = Fintype.card (Sym2 V) := by simp
  let S : Finset ℕ := (Finset.range (N + 1)).filter fun n =>
    ∃ H, P H ∧ H.edgeSet.ncard = n
  have hS : S.Nonempty := by
    refine ⟨G.edgeSet.ncard, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hbound G), ⟨G, hG, rfl⟩⟩
  let m : ℕ := S.max' hS
  have hm : m ∈ S := by
    exact Finset.max'_mem S hS
  obtain ⟨H, hH, hHm⟩ := (Finset.mem_filter.mp hm).2
  refine ⟨H, hH, ?_⟩
  intro M hM
  have hmem : M.edgeSet.ncard ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hbound M), ⟨M, hM, rfl⟩⟩
  have hle : M.edgeSet.ncard ≤ m := by
    dsimp [m]
    exact Finset.le_max' S M.edgeSet.ncard hmem
  simpa [m, hHm] using hle

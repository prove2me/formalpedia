-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_edgeFinset_card__p2m_a0b09a49_72c3_4535_856d_a54b174f4bb7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:24:00.375757+00:00
-- url     : https://prove2.me/submissions/38b6854f-58d6-4f4d-8a9d-c2a563f27027

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (P : SimpleGraph V → Prop) (hK : P K) (N : Nat)
    (hbound : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], P G → G.edgeFinset.card ≤ N) :
    ∃ L : SimpleGraph V, P L ∧ ∃ dL : DecidableRel L.Adj,
      letI : DecidableRel L.Adj := dL
      K.edgeFinset ⊆ L.edgeFinset ∧
        ∀ (M : SimpleGraph V) [DecidableRel M.Adj],
          P M → L.edgeFinset ⊆ M.edgeFinset →
            M.edgeFinset.card ≤ L.edgeFinset.card := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => P G ∧ K.edgeSet ⊆ G.edgeSet)
  have hadmissible : admissible.Nonempty := by
    refine ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK, ?_⟩⟩
    exact Set.Subset.rfl
  obtain ⟨L, hL, hmax⟩ :=
    Finset.exists_max_image admissible (fun G => G.edgeSet.ncard) hadmissible
  rcases Finset.mem_filter.mp hL with ⟨_, hPL, hKLset⟩
  refine ⟨L, hPL, (inferInstance : DecidableRel L.Adj), ?_⟩
  constructor
  · intro e he
    have he' : e ∈ K.edgeSet := by
      simpa [SimpleGraph.edgeFinset] using he
    have hmem : e ∈ L.edgeSet := hKLset he'
    simpa [SimpleGraph.edgeFinset] using hmem
  · intro M _dM hPM hLM
    have hLMset : L.edgeSet ⊆ M.edgeSet := by
      intro e he
      have he' : e ∈ L.edgeFinset := by
        simpa [SimpleGraph.edgeFinset] using he
      have hm : e ∈ M.edgeFinset := hLM he'
      simpa [SimpleGraph.edgeFinset] using hm
    have hmem : M ∈ admissible := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hPM, hKLset.trans hLMset⟩
    have hcard : M.edgeFinset.card = M.edgeSet.ncard := by
      simp [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
    have hLcard : L.edgeFinset.card = L.edgeSet.ncard := by
      simp [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
    rw [hcard, hLcard]
    exact hmax M hmem

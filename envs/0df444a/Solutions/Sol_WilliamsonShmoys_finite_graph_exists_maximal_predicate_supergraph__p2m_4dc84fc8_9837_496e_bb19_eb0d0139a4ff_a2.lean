-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_exists_maximal_predicate_supergraph__p2m_4dc84fc8_9837_496e_bb19_eb0d0139a4ff_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:38:50.207985+00:00
-- url     : https://prove2.me/submissions/1f824ec1-3bf2-4264-bd91-18a0d689a3a5

import Mathlib
set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P L) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ M : SimpleGraph V,
      L.edgeFinset ⊆ M.edgeFinset ∧
      P M ∧
      ∀ N : SimpleGraph V,
        (∀ u v, M.Adj u v → N.Adj u v) →
        P N →
        ∀ u v, N.Adj u v → M.Adj u v := by
  classical
  let s : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => L ≤ G ∧ P G
  have hs : s.Nonempty := by
    refine ⟨L, ?_⟩
    simp [s, hP]
  obtain ⟨M, hM, hmax⟩ :=
    Finset.exists_max_image s (fun G => G.edgeFinset.card) hs
  have hLM : L ≤ M := (Finset.mem_filter.mp hM).2.1
  have hPM : P M := (Finset.mem_filter.mp hM).2.2
  refine ⟨M, SimpleGraph.edgeFinset_subset_edgeFinset.mpr hLM, hPM, ?_⟩
  intro N hMN hPN u v hNuv
  have hMleN : M ≤ N := SimpleGraph.le_iff_adj.mpr hMN
  have hLN : L ≤ N := le_trans hLM hMleN
  have hNmem : N ∈ s := by
    simp [s, hLN, hPN]
  have hcard : N.edgeFinset.card ≤ M.edgeFinset.card := hmax N hNmem
  have hsub : M.edgeFinset ⊆ N.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.mpr hMleN
  have hEq : M.edgeFinset = N.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have hEqGraph : M = N := SimpleGraph.edgeFinset_inj.mp hEq
  rw [← hEqGraph] at hNuv
  exact hNuv
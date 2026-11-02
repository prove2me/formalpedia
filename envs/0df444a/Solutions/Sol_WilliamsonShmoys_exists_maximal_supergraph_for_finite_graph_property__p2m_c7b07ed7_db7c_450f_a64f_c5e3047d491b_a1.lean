-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_finite_graph_property__p2m_c7b07ed7_db7c_450f_a64f_c5e3047d491b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:56:13.123477+00:00
-- url     : https://prove2.me/submissions/25ab0a98-3288-47ed-a9d5-f00e701c07f1

import Mathlib

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hK : P K) :
    ∃ L : SimpleGraph V, P L ∧ K ≤ L ∧
      ∀ M : SimpleGraph V, P M → L ≤ M → M = L := by
  classical
  letI : Finite (SimpleGraph V) :=
    Finite.of_injective (fun G : SimpleGraph V => G.edgeFinset) (by
      intro G H h
      exact SimpleGraph.edgeFinset_inj.mp h)
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let Q : SimpleGraph V → Prop := fun G => P G ∧ K ≤ G
  let s : Finset (SimpleGraph V) := Finset.univ.filter Q
  have hKmem : K ∈ s := by
    simp [s, Q, hK]
  have hs : s.Nonempty := ⟨K, hKmem⟩
  obtain ⟨L, hLs, hmax⟩ :=
    Finset.exists_max_image s (fun G : SimpleGraph V => G.edgeFinset.card) hs
  have hLQ : Q L := (Finset.mem_filter.mp hLs).2
  have hL : P L ∧ K ≤ L := hLQ
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hPM hLM
  have hQM : Q M := ⟨hPM, hL.2.trans hLM⟩
  have hMs : M ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQM⟩
  have hcard : M.edgeFinset.card ≤ L.edgeFinset.card := hmax M hMs
  have hedge : L.edgeFinset = M.edgeFinset :=
    Finset.eq_of_subset_of_card_le
      (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hLM) hcard
  exact (SimpleGraph.edgeFinset_inj.mp hedge).symm
-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_max_edge_ncard__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:59:28.845994+00:00
-- url     : https://prove2.me/submissions/73f5a6f1-fcc6-415b-934c-e2e1b7a67bd1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V =>
      L <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      forall N : SimpleGraph V,
        L <= N ->
        WilliamsonShmoys.HasPlanarDrawingOn N ->
        N.edgeSet.ncard <= M.edgeSet.ncard := by
  classical
  have hbound (G : SimpleGraph V) :
      G.edgeSet.ncard <= Fintype.card (Sym2 V) := by
    calc
      G.edgeSet.ncard <= (Set.univ : Set (Sym2 V)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
      _ = Fintype.card (Sym2 V) := by simp
  let candidates : Finset Nat :=
    (Finset.range (Fintype.card (Sym2 V) + 1)).filter fun n =>
      Exists fun G : SimpleGraph V =>
        L <= G /\ WilliamsonShmoys.HasPlanarDrawingOn G /\ G.edgeSet.ncard = n
  have hne : candidates.Nonempty := by
    have hLmem : L.edgeSet.ncard ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_range]
      constructor
      · have hb := hbound L
        omega
      · exact ⟨L, le_rfl, hL, rfl⟩
    exact ⟨L.edgeSet.ncard, hLmem⟩
  let k := candidates.max' hne
  have hk_mem : k ∈ candidates := Finset.max'_mem candidates hne
  have hk_parts := Finset.mem_filter.mp hk_mem
  let mWitness : Exists fun G : SimpleGraph V =>
      L <= G /\ WilliamsonShmoys.HasPlanarDrawingOn G /\ G.edgeSet.ncard = k := hk_parts.2
  let M := Classical.choose mWitness
  have hMw := Classical.choose_spec mWitness
  refine ⟨M, ?_⟩
  refine ⟨hMw.1, hMw.2.1, ?_⟩
  intro N hLN hN
  have hn_mem : N.edgeSet.ncard ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_range]
    constructor
    · have hb := hbound N
      omega
    · exact ⟨N, hLN, hN, rfl⟩
  have hle : N.edgeSet.ncard <= k :=
    Finset.le_max' candidates N.edgeSet.ncard hn_mem
  rw [hMw.2.2]
  exact hle

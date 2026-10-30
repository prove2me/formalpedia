-- Prove2me | solution 1 for WilliamsonShmoys.eq_of_subgraph_and_edge_card_le__p2m_3e744d16_fd12_4405_889b_d7d7bae50b90_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:39:27.917985+00:00
-- url     : https://prove2.me/submissions/180bcaa7-3f58-455b-8e62-e0b0abe7300c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H)
    (hcard : Nat.card {e : Sym2 V // e ∈ H.edgeSet} ≤
      Nat.card {e : Sym2 V // e ∈ G.edgeSet}) : G = H := by
  classical
  by_contra hne
  have hsub : G.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_mono hGH
  have hnot : ¬ G.edgeSet = H.edgeSet := by
    intro he
    exact hne (SimpleGraph.edgeSet_inj.mp he)
  have hss : G.edgeSet ⊂ H.edgeSet :=
    Set.ssubset_iff_subset_ne.mpr ⟨hsub, hnot⟩
  have hlt : G.edgeSet.ncard < H.edgeSet.ncard :=
    Set.ncard_lt_ncard hss (Set.toFinite H.edgeSet)
  have hcard' : Nat.card {e : Sym2 V // e ∈ G.edgeSet} <
      Nat.card {e : Sym2 V // e ∈ H.edgeSet} := by
    simpa only [Nat.card_coe_set_eq] using hlt
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_edge_maximal_supergraph_same_vertex
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:07:14.902824+00:00
-- url     : https://prove2.me/submissions/c2fc682e-ca7d-472f-aa0e-3ce4287a4c68

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_max_edgeCard_graph
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_lt_of_le_of_ne

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
  classical
  let edgeFinite : ∀ G : SimpleGraph V, Fintype G.edgeSet :=
    fun G => Fintype.ofFinite G.edgeSet
  obtain ⟨M, hM, hMax⟩ :=
    WilliamsonShmoys.exists_max_edgeCard_graph edgeFinite
      (fun G : SimpleGraph V => L ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
      ⟨L, le_rfl, hDrawing⟩
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro N hMN hN
  by_contra hne
  have hlt := WilliamsonShmoys.edgeFinset_card_lt_of_le_of_ne
    (edgeFinite M) (edgeFinite N) hMN hne
  have hle := hMax N ⟨hM.1.trans hMN, hN⟩
  omega
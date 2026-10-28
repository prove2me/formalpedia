-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_edge_count_v4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:00:04.766426+00:00
-- url     : https://prove2.me/submissions/cc92a769-18ee-40cf-ae15-70da809dda11
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_triangulated_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard ≤ L.edgeSet.ncard) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hMcard⟩ :=
    WilliamsonShmoys.exists_drawable_triangulated_supergraph L hV hL
  have hEdgeSubset : L.edgeSet ⊆ M.edgeSet := SimpleGraph.edgeSet_mono hLM
  have hupper : L.edgeSet.ncard ≤ M.edgeSet.ncard :=
    Set.ncard_le_ncard hEdgeSubset
  have hlower : 3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
    rw [← hMcard]
    exact hmax M hLM hM
  omega
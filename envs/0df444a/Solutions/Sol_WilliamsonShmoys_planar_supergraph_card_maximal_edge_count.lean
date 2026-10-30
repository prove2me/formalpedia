-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_card_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:13:14.604597+00:00
-- url     : https://prove2.me/submissions/17379d1a-1e40-48c6-9fe7-a9b4f2c948d5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_triangulated_supergraph_v10

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M ->
      M.edgeSet.ncard <= L.edgeSet.ncard) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hTri⟩ :=
    WilliamsonShmoys.drawable_triangulated_supergraph_v10 L hV hL
  have hML : M.edgeSet.ncard <= L.edgeSet.ncard := hmax M hLM hM
  have hLMcard : L.edgeSet.ncard <= M.edgeSet.ncard :=
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hLM)
  have hEq : L.edgeSet.ncard = M.edgeSet.ncard := Nat.le_antisymm hLMcard hML
  omega
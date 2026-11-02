-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_23689463_5c07_4e0b_a29b_546de8e1e4a9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:48:25.782429+00:00
-- url     : https://prove2.me/submissions/fbb08b61-23fc-43dc-b988-44604de3b523
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_supergraph__p2m_a3a0b559_5297_496f_932d_5e752a281600_a1
import Mathlib
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L) (hcard : 3 <= Fintype.card V)
    (hmax : forall (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      L <= M -> HasPlanarDrawingOn M -> M <= L) :
    3 * Fintype.card V <= L.edgeFinset.card + 6 := by
  obtain ⟨M, dM, hLM, hM, hEdges⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulated_supergraph__p2m_a3a0b559_5297_496f_932d_5e752a281600_a1
      L dL hL hcard
  have hML : M <= L := hmax M dM hLM hM
  have hMcard_le : M.edgeFinset.card <= L.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hML)
  have hLcard_le : L.edgeFinset.card <= M.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hLM)
  have hEdgeCard : M.edgeFinset.card = L.edgeFinset.card :=
    Nat.le_antisymm hMcard_le hLcard_le
  omega
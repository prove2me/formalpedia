-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_8d0b95f1_3d22_423b_9850_63148fea79a7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T09:27:15.562054+00:00
-- url     : https://prove2.me/submissions/8a9c4801-9c54-4827-b726-060feddae903

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a7a27be2_fbb8_44ae_9ce4_aea6abd1f255_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hLDrawing : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  have hmax' : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L := by
    intro M hLM hM
    rw [hmax M hLM hM]
  have hEuler := WilliamsonShmoys.maximal_planar_edge_count__p2m_a7a27be2_fbb8_44ae_9ce4_aea6abd1f255_a1
    L hLDrawing hcard hmax'
  have hCard : L.edgeFinset.card = L.edgeSet.ncard := by
    calc
      L.edgeFinset.card = Fintype.card L.edgeSet :=
        (SimpleGraph.card_edgeSet (G := L)).symm
      _ = L.edgeSet.ncard := Set.fintypeCard_eq_ncard L.edgeSet
  rw [hCard]
  omega

-- Prove2me | solution 1 for WilliamsonShmoys.planarDisconnectedComponentCounts__p2m_db85b882_89e6_4feb_9146_2311e309823a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:37:44.586888+00:00
-- url     : https://prove2.me/submissions/8b485a8e-15b9-4053-b76d-d696e6e4cbf3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connectedComponent_partition_data__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_induce__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : ¬ L.Connected) :
    ∃ (C : Finset (Finset V)) (edgeCount : Finset V → Nat),
      2 ≤ C.card ∧
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∑ s ∈ C, edgeCount s) = (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) ∧
      (∀ s ∈ C, edgeCount s + 3 ≤ 3 * s.card) := by
  classical
  letI : DecidableRel L.Adj := dL
  obtain ⟨C, edgeCount, hcard, hnonempty, hcover, hdisjoint, hvertices, hedges,
      hedgeCount, hconnected⟩ :=
    WilliamsonShmoys.connectedComponent_partition_data__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
      L dL hconn
  have hbound : ∀ s ∈ C, edgeCount s + 3 ≤ 3 * s.card := by
    intro s hs
    have hp :=
      WilliamsonShmoys.planarDrawingOn_induce__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
        L hL s
    have hb :=
      WilliamsonShmoys.connected_planar_edge_bound__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
        (L.induce (↑s : Set V)) inferInstance hp (hconnected s hs)
    rw [hedgeCount s hs]
    simpa using hb
  exact ⟨C, edgeCount, hcard, hnonempty, hcover, hdisjoint, hvertices, hedges, hbound⟩
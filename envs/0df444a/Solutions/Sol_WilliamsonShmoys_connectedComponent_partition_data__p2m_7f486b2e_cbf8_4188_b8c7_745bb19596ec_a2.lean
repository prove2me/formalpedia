-- Prove2me | solution 1 for WilliamsonShmoys.connectedComponent_partition_data__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:05:50.745103+00:00
-- url     : https://prove2.me/submissions/40c04c2b-bef7-461f-9b54-72bc3706501e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connectedComponent_partition_blocks__p2m_1c5fc6d8_f74d_4a49_af67_c6124a04288f_a1
import Theorems.Thm_WilliamsonShmoys_connectedComponent_edge_conservation_disjoint__p2m_1c5fc6d8_f74d_4a49_af67_c6124a04288f_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hconn : ¬ L.Connected) :
    (letI : DecidableRel L.Adj := dL;
    ∃ (C : Finset (Finset V)) (edgeCount : Finset V → Nat),
      2 ≤ C.card ∧
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∑ s ∈ C, edgeCount s) = L.edgeFinset.card ∧
      (∀ s ∈ C, edgeCount s = (L.induce (↑s : Set V)).edgeFinset.card) ∧
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected)) := by
  letI : DecidableRel L.Adj := dL
  obtain ⟨C, hcard, hne, hcover, hdisj, hverts, hpair, hconnected⟩ :=
    WilliamsonShmoys.connectedComponent_partition_blocks__p2m_1c5fc6d8_f74d_4a49_af67_c6124a04288f_a1 L dL hconn
  let edgeCount : Finset V → Nat := fun s => (L.induce (↑s : Set V)).edgeFinset.card
  refine ⟨C, edgeCount, hcard, hne, hcover, hdisj, hverts, ?_, ?_, hconnected⟩
  · exact WilliamsonShmoys.connectedComponent_edge_conservation_disjoint__p2m_1c5fc6d8_f74d_4a49_af67_c6124a04288f_a2 L dL C hdisj hpair
  · intro s hs
    rfl
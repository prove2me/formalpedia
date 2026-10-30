-- Prove2me | solution 1 for WilliamsonShmoys.component_edge_data__p2m_66ed8684_7720_4905_99a4_14d61ffeb91a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:38:16.987215+00:00
-- url     : https://prove2.me/submissions/609e5728-1f45-46ad-91d0-6a2dd9a94bdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_vertex_accounting__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a3
import Theorems.Thm_WilliamsonShmoys_component_edge_bounds__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a3
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    [Fintype L.ConnectedComponent]
    (hLocal : forall (S : Finset V), 3 <= S.card ->
      (L.induce (↑ S : Set V)).Connected ->
      (L.induce (↑ S : Set V)).edgeSet.ncard + 6 <= 3 * S.card) :
    exists n e : L.ConnectedComponent -> Nat,
      (Finset.univ.sum fun c => n c) = Fintype.card V /\
      (Finset.univ.sum fun c => e c) = L.edgeSet.ncard /\
      (forall c, 1 <= n c) /\
      (forall c, n c <= 2 -> e c <= 1) /\
      (forall c, 3 <= n c -> e c + 6 <= 3 * n c) := by
  let n : L.ConnectedComponent -> Nat := fun c => c.supp.ncard
  let e : L.ConnectedComponent -> Nat := fun c => (L.induce c.supp).edgeSet.ncard
  obtain ⟨hnv, hev, hpos⟩ :=
    WilliamsonShmoys.component_vertex_accounting__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a3 L
  have hb := WilliamsonShmoys.component_edge_bounds__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a3 L hLocal
  refine ⟨n, e, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [n] using hnv
  · simpa [e] using hev
  · intro c
    simpa [n] using hpos c
  · exact fun c hc => hb.1 c hc
  · exact fun c hc => hb.2 c hc
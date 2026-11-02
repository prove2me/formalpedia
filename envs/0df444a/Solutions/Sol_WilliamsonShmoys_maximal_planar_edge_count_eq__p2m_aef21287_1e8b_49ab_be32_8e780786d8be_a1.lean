-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_aef21287_1e8b_49ab_be32_8e780786d8be_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:40:10.925404+00:00
-- url     : https://prove2.me/submissions/f5764a7f-cdc9-48b5-8d4f-105d8732094e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_triangulation__p2m_ff906063_5ccb_4e8b_ad72_9b52b363ab18_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : L.Connected)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M <= L) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  obtain ⟨M, hLM, hM, hMcard⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_triangulation__p2m_ff906063_5ccb_4e8b_ad72_9b52b363ab18_a1
      L hcard hconn hL
  have hML : M <= L := hmax M hLM hM
  have hEq : M = L := le_antisymm hML hLM
  rw [← hEq]
  exact hMcard
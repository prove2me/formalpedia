-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_1450b57d_ff3f_4f0e_9779_6941f1e67e4b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T23:11:41.728681+00:00
-- url     : https://prove2.me/submissions/ecee079a-8be5-4c97-9036-dd56b3db89b2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeFinset.card ≤ H.edgeFinset.card := by
  classical
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  obtain ⟨H, hAdj, hconn, hHdraw, _⟩ :=
    WilliamsonShmoys.connected_planar_supergraph K hcard hdraw
  have hle : K ≤ H := fun u v huv => hAdj u v huv
  refine ⟨H, hle, hconn, hHdraw, ?_⟩
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hle)

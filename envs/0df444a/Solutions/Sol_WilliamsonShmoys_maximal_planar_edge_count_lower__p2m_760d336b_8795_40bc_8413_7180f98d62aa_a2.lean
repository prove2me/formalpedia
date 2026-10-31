-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_760d336b_8795_40bc_8413_7180f98d62aa_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:15:02.037417+00:00
-- url     : https://prove2.me/submissions/808c9aa2-13d3-451d-8aaa-858c3b99bad3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_e0d9ce97_e019_42af_a0bd_4118a7b4d4c1_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hmax : forall (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      (letI : DecidableRel L.Adj := dL
       H <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= H))
    (hcard : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= H.edgeFinset.card := by
  letI : DecidableRel H.Adj := dH
  obtain ⟨L, dL, hHL, hLplanar, hLcard⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_e0d9ce97_e019_42af_a0bd_4118a7b4d4c1_a1
      H dH hH hcard
  letI : DecidableRel L.Adj := dL
  have hLH : L <= H := hmax L dL hHL hLplanar
  have hedge : L.edgeFinset ⊆ H.edgeFinset := SimpleGraph.edgeFinset_mono hLH
  have hcount : L.edgeFinset.card ≤ H.edgeFinset.card := Finset.card_le_card hedge
  omega
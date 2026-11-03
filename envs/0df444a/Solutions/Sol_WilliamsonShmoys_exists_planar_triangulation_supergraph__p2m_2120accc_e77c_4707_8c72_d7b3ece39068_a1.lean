-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_2120accc_e77c_4707_8c72_d7b3ece39068_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:14:57.46421+00:00
-- url     : https://prove2.me/submissions/72ca670a-f3f2-4fcb-8781-eca673b10923

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_6467164a_4ac7_4202_bbd8_0cd7677d3ce4_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6467164a_4ac7_4202_bbd8_0cd7677d3ce4_a2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     Exists fun H : SimpleGraph V =>
       And (N <= H)
         (And (WilliamsonShmoys.HasPlanarDrawingOn H)
           (letI : DecidableRel H.Adj := Classical.decRel H.Adj
            H.edgeFinset.card + 6 = 3 * Fintype.card V))) := by
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  obtain ⟨H, hNH, hHplanar, hHmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_6467164a_4ac7_4202_bbd8_0cd7677d3ce4_a2
      N hN hcard
  refine ⟨H, hNH, hHplanar, ?_⟩
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_6467164a_4ac7_4202_bbd8_0cd7677d3ce4_a2
    H hHplanar hHmax hcard
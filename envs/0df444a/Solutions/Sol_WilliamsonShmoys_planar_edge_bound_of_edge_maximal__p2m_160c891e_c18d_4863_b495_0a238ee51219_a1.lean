-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_of_edge_maximal__p2m_160c891e_c18d_4863_b495_0a238ee51219_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:48:53.133748+00:00
-- url     : https://prove2.me/submissions/f5fe4b70-fd0d-454b-bd28-fb92242957f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_b9887391_36ac_4b13_9489_3daf1e406adb_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K →
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : Fintype ↥K.edgeSet := Fintype.ofFinite _
       letI : DecidableRel N.Adj := Classical.decRel N.Adj
       letI : Fintype ↥N.edgeSet := Fintype.ofFinite _
       K.edgeFinset.card ≤ N.edgeFinset.card)) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     letI : Fintype ↥N.edgeSet := Fintype.ofFinite _
     3 * Fintype.card V ≤ N.edgeFinset.card + 6) := by
  classical
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  letI : Fintype ↥N.edgeSet := Fintype.ofFinite _
  obtain ⟨K, hNK, hK, hcard⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_b9887391_36ac_4b13_9489_3daf1e406adb_a1
      N hN hV
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  letI : Fintype ↥K.edgeSet := Fintype.ofFinite _
  have hle := hmax K hNK hK
  omega
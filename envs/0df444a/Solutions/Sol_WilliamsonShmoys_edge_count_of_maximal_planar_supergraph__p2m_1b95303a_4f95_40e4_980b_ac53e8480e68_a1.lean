-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_supergraph__p2m_1b95303a_4f95_40e4_980b_ac53e8480e68_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:30:45.939854+00:00
-- url     : https://prove2.me/submissions/3472520f-2868-48e4-808e-b867a8df6fbb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_triangulation_count__p2m_1625d03f_5f98_459a_8070_43608692433f_a2
import Mathlib

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K) (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) [DecidableRel L.Adj], K ≤ L →
      HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V = K.edgeFinset.card + 6 := by
  letI : DecidableRel K.Adj := dK
  obtain ⟨L, dL, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_with_triangulation_count__p2m_1625d03f_5f98_459a_8070_43608692433f_a2 K dK hK hcard
  letI : DecidableRel L.Adj := dL
  have hLK : L = K := hmax L hKL hL
  have hedge : L.edgeFinset = K.edgeFinset :=
    SimpleGraph.edgeFinset_inj.mpr hLK
  calc
    3 * Fintype.card V = L.edgeFinset.card + 6 := hcount
    _ = K.edgeFinset.card + 6 := by rw [hedge]
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_e5af1f58_1baf_49a9_bfe1_0313f8cb5edc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:36:04.828847+00:00
-- url     : https://prove2.me/submissions/d3edc966-4b86-483e-9dd9-40ec25d49cf6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_extension__p2m_73c1177f_a9a7_4995_aff4_29e76100000f_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L = K)
    (hcard : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= K.edgeFinset.card := by
  obtain ⟨L, hKL, hLplanar, dL, hLcount⟩ :=
    WilliamsonShmoys.maximal_planar_edge_count_extension__p2m_73c1177f_a9a7_4995_aff4_29e76100000f_a1
      K hK hcard
  letI : DecidableRel L.Adj := dL
  have hLK : L = K := hmax L hKL hLplanar
  have hLcount' : 3 * Fintype.card V - 6 <= Fintype.card L.edgeSet := by
    simpa only [SimpleGraph.edgeFinset_card] using hLcount
  have hKcount : 3 * Fintype.card V - 6 <= Fintype.card K.edgeSet := by
    simpa only [hLK] using hLcount'
  simpa only [SimpleGraph.edgeFinset_card] using hKcount
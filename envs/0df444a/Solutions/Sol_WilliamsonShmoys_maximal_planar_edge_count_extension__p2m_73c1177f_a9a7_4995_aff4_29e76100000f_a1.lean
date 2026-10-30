-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_extension__p2m_73c1177f_a9a7_4995_aff4_29e76100000f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:49:35.9511+00:00
-- url     : https://prove2.me/submissions/fb31deb5-8e4a-4443-941e-6525f639fc61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_316c89ef_5381_45bf_ad7e_e8d13020052b_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_316c89ef_5381_45bf_ad7e_e8d13020052b_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∃ (_ : DecidableRel L.Adj),
        3 * Fintype.card V - 6 ≤ L.edgeFinset.card := by
  obtain ⟨L, hKL, hL, hmaxData⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_316c89ef_5381_45bf_ad7e_e8d13020052b_a2
      K hK hcard
  obtain ⟨instL, hmax⟩ := hmaxData
  obtain ⟨instBound, hedge⟩ :=
    WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_316c89ef_5381_45bf_ad7e_e8d13020052b_a2
      L hL hmax hcard
  exact ⟨L, hKL, hL, instBound, hedge⟩
-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_caf31ad8_7627_4591_a986_7fd32a9eba8e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:36:12.425238+00:00
-- url     : https://prove2.me/submissions/f78a0116-1647-40d7-9beb-04495e42888c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_bcbd7a83_d291_4735_8d53_f72682e52b0d_a1
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count__p2m_bcbd7a83_d291_4735_8d53_f72682e52b0d_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (letI : DecidableRel N.Adj := dN;
        N.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨N, dN, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph__p2m_bcbd7a83_d291_4735_8d53_f72682e52b0d_a1
      M hM hcard
  have hcount :=
    WilliamsonShmoys.planar_maximal_edge_count__p2m_bcbd7a83_d291_4735_8d53_f72682e52b0d_a1
      N dN hN hmax hcard
  exact ⟨N, dN, hMN, hN, hcount⟩
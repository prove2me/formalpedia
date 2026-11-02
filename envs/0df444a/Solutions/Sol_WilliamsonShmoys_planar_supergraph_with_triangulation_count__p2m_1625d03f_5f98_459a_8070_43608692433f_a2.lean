-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_triangulation_count__p2m_1625d03f_5f98_459a_8070_43608692433f_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:48:39.325253+00:00
-- url     : https://prove2.me/submissions/e3bac9ca-4e26-4940-a347-75c8ae0d5965
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_b79a3d22_514c_40c6_b0d9_3192cd4e6368_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_b79a3d22_514c_40c6_b0d9_3192cd4e6368_a1

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K) (hcard : 3 ≤ Fintype.card V) :
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      K ≤ L ∧ HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeFinset.card + 6 := by
  obtain ⟨L, dL, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_b79a3d22_514c_40c6_b0d9_3192cd4e6368_a1
      K dK hK
  exact ⟨L, dL, hKL, hL,
    WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_b79a3d22_514c_40c6_b0d9_3192cd4e6368_a1
      L dL hL hcard hmax⟩
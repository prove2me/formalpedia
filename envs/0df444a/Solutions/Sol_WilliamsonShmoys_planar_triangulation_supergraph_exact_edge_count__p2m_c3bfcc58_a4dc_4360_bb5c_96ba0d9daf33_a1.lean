-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_c3bfcc58_a4dc_4360_bb5c_96ba0d9daf33_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:43:48.278677+00:00
-- url     : https://prove2.me/submissions/afb11d5d-f69c-48e3-8168-5bfe8c97988a

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_14b8c227_b724_4de5_85b9_cdf4d661eb0f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_14b8c227_b724_4de5_85b9_cdf4d661eb0f_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧ HasPlanarDrawingOn P ∧
      (letI : DecidableRel P.Adj := Classical.decRel P.Adj;
        3 * Fintype.card V = P.edgeFinset.card + 6) := by
  obtain ⟨P, hNP, hP, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_14b8c227_b724_4de5_85b9_cdf4d661eb0f_a1 N hV hN
  exact ⟨P, hNP, hP,
    WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_14b8c227_b724_4de5_85b9_cdf4d661eb0f_a1 P hV hP hmax⟩
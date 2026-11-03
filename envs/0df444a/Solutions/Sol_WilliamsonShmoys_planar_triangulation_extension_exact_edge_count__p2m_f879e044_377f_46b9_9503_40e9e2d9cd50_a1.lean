-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_exact_edge_count__p2m_f879e044_377f_46b9_9503_40e9e2d9cd50_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:48:32.756234+00:00
-- url     : https://prove2.me/submissions/60682e26-97a8-43a6-8ec7-396b13e825a7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists__p2m_71c4bf82_58f5_4c33_a47c_7b17640d4f06_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_71c4bf82_58f5_4c33_a47c_7b17640d4f06_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    Exists (fun N : SimpleGraph V => M <= N ∧ HasPlanarDrawingOn N ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
       N.edgeFinset.card + 6 = 3 * Fintype.card V)) := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_71c4bf82_58f5_4c33_a47c_7b17640d4f06_a2
      M hM
  have hcard :=
    WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_71c4bf82_58f5_4c33_a47c_7b17640d4f06_a2
      N hV hN hmax
  exact ⟨N, hMN, hN, hcard⟩
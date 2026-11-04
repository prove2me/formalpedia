-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f84a2b8d_758d_48e3_856e_f835c2dfd776_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:38:42.903184+00:00
-- url     : https://prove2.me/submissions/c9329c6f-6f4d-4b17-88a5-f32560d6ebc1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_c3bfcc58_a4dc_4360_bb5c_96ba0d9daf33_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
      3 * Fintype.card V ≤ N.edgeFinset.card + 6) := by
  classical
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  obtain ⟨P, hNP, hP, hcard⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_c3bfcc58_a4dc_4360_bb5c_96ba0d9daf33_a1
      N hV hN
  have hPN : P = N := hmax P hNP hP
  rw [hPN] at hcard
  omega
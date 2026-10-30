-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_equations__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:08:11.441789+00:00
-- url     : https://prove2.me/submissions/aa177d0e-8478-4976-8410-5a2b6431919b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound__p2m_e307fd83_c86f_42f7_8879_0524310903cd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_e307fd83_c86f_42f7_8879_0524310903cd_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : forall K : SimpleGraph V,
      LE.le G K -> WilliamsonShmoys.HasPlanarDrawingOn K -> LE.le K G)
    (hV : LE.le 3 (Fintype.card V)) :
    Exists fun f : Nat =>
      And (Fintype.card V + f = G.edgeSet.ncard + 2)
          (3 * f = 2 * G.edgeSet.ncard) := by
  have hUpper := WilliamsonShmoys.maximal_planar_edge_count_upper_bound__p2m_e307fd83_c86f_42f7_8879_0524310903cd_a1
    G hG hV
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e307fd83_c86f_42f7_8879_0524310903cd_a1
    G hG hMax hV
  have hEdges : G.edgeSet.ncard + 6 = 3 * Fintype.card V := by omega
  refine Exists.intro (2 * Fintype.card V - 4) ?_
  refine And.intro ?_ ?_ <;> omega
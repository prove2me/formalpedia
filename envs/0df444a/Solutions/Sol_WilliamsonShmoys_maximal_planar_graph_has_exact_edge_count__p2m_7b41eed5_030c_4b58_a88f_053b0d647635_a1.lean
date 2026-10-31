-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_7b41eed5_030c_4b58_a88f_053b0d647635_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:14.697388+00:00
-- url     : https://prove2.me/submissions/e05a9e12-40a6-4b59-ad34-4f98161351c3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_has_triangulation_completion__p2m_0cd2651d_edaf_48bf_b0c6_7823a1c2bf88_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 <= Fintype.card V) (hT : HasPlanarDrawingOn T) (hmax : forall U : SimpleGraph V, T <= U -> HasPlanarDrawingOn U -> U <= T) : 3 * Fintype.card V - 6 = T.edgeSet.ncard := by
  obtain ⟨U, hTU, hU, hcount⟩ := WilliamsonShmoys.planar_drawing_on_has_triangulation_completion__p2m_0cd2651d_edaf_48bf_b0c6_7823a1c2bf88_a2 T hV hT
  have hUT : U <= T := hmax U hTU hU
  have hEq : U = T := le_antisymm hUT hTU
  simpa [hEq] using hcount
-- Prove2me | solution 1 for WilliamsonShmoys.WilliamsonShmoys_planar_graph_edge_extension__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:49:55.131098+00:00
-- url     : https://prove2.me/submissions/31b06df9-f06f-4ebc-8e3e-3cbb337d64e6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_WilliamsonShmoys_maximal_drawable_extension__p2m_0ce6e58c_926f_4660_b10f_ba8df60d96d0_a2
import Theorems.Thm_WilliamsonShmoys_WilliamsonShmoys_maximal_drawable_edge_count__p2m_0ce6e58c_926f_4660_b10f_ba8df60d96d0_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hP : HasPlanarDrawingOn P)
    (hlt : (letI : DecidableRel P.Adj := Classical.decRel P.Adj;
      P.edgeFinset.card + 6 < 3 * Fintype.card V)) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ ¬ Q ≤ P ∧ HasPlanarDrawingOn Q := by
  classical
  obtain ⟨Q, hPQ, hQ, hmax⟩ :=
    WilliamsonShmoys.WilliamsonShmoys_maximal_drawable_extension__p2m_0ce6e58c_926f_4660_b10f_ba8df60d96d0_a2 P hP
  have hcount :=
    WilliamsonShmoys.WilliamsonShmoys_maximal_drawable_edge_count__p2m_0ce6e58c_926f_4660_b10f_ba8df60d96d0_a2 Q hV hQ hmax
  refine ⟨Q, hPQ, ?_, hQ⟩
  intro hQP
  have hEq : Q = P := le_antisymm hQP hPQ
  subst Q
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.connected_maximal_drawable_edge_count__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:53:46.961555+00:00
-- url     : https://prove2.me/submissions/09b146a6-db30-42f0-a732-8f550d6a58df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extends_to_triangulation__p2m_6ce17d90_7e34_4ced_9818_f205b3115d6a_a1
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : P.Connected)
    (hP : HasPlanarDrawingOn P)
    (hMax : ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P) :
    P.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Q, hPQ, hQ, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_6ce17d90_7e34_4ced_9818_f205b3115d6a_a1
      P hV hP
  have hQP : Q ≤ P := hMax Q hPQ hQ
  have hEq : Q = P := le_antisymm hQP hPQ
  rw [← hEq]
  exact hcount
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_face_equations_e86e41b9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:30:06.072924+00:00
-- url     : https://prove2.me/submissions/a330dc43-ef91-4cf1-a431-d1e6ab649aeb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_for_face_equations_e86e41b9

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M = L)
    (hCard : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = L.edgeSet.ncard + 2 /\
        3 * f = 2 * L.edgeSet.ncard := by
  have hE :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count_for_face_equations_e86e41b9
      L hL hMax hCard
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega

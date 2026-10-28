-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_euler_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:27:26.982039+00:00
-- url     : https://prove2.me/submissions/46e65fb3-d7be-46e1-a26f-87a15078d94b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T <= U →
      WilliamsonShmoys.HasPlanarDrawingOn U → U <= T) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hU⟩ :=
    WilliamsonShmoys.drawable_triangulation_edge_count T hV hT
  rcases hU with ⟨hTU, hU⟩
  rcases hU with ⟨hUdraw, hUcount⟩
  have hEq : U = T := le_antisymm (hmax U hTU hUdraw) hTU
  simpa [hEq] using hUcount
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_818bf149_0bfd_4348_866a_626aa910ef08
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:48:50.448787+00:00
-- url     : https://prove2.me/submissions/4e467b00-4b34-4488-a3bc-5bc74d34d1dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T)
    (hV : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hTK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_edge_count T hT hV
  have hKT : K = T := hmax K hTK hK
  simpa [hKT] using hcount
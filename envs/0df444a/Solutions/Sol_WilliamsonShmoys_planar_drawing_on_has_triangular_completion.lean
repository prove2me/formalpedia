-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_has_triangular_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:02:10.493962+00:00
-- url     : https://prove2.me/submissions/c98aed68-e9c8-466e-9786-e53c0857f0b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_maximal_planar_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_triangular_map

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V), G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ (m : Nat), Nonempty (WilliamsonShmoys.TriangularMap K (Fin m)) := by
  obtain ⟨K, hGK, hplanar, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_on_maximal_planar_extension G hG hV
  obtain ⟨m, hmap⟩ :=
    WilliamsonShmoys.maximal_planar_graph_has_triangular_map K hplanar hV hmax
  exact ⟨K, hGK, hplanar, m, hmap⟩
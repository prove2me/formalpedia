-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_85252b40_ee02_4664_960a_c8af730317d2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:23:13.489416+00:00
-- url     : https://prove2.me/submissions/21323c92-a33b-482b-b756-490b527eb7f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extend_to_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_has_triangular_faces

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      WilliamsonShmoys.HasTriangularPlaneFaceSystem K := by
  obtain ⟨K, hHK, hKPlanar, hMaximal⟩ :=
    WilliamsonShmoys.planar_drawing_extend_to_maximal_supergraph H hV hH
  exact ⟨K, hHK, hKPlanar,
    WilliamsonShmoys.maximal_planar_supergraph_has_triangular_faces K hV hKPlanar hMaximal⟩
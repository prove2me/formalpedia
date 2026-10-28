-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_for_job_3a7ba4e8_8a44_4d12_bfa9_d180fa091eca
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:16:14.07082+00:00
-- url     : https://prove2.me/submissions/b6e01a5d-4e56-4493-a9f3-9639e477438f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_same_vertices

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_same_vertices H hV hH
  have hKH : K = H := hmax K hHK hK
  simpa [hKH] using hcount
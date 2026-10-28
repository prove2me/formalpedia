-- Prove2me | solution 1 for WilliamsonShmoys.same_vertex_planar_extension_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:40:22.353194+00:00
-- url     : https://prove2.me/submissions/79daf934-6049-4249-a734-da3d2678d047
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_extension_maximal
import Theorems.Thm_WilliamsonShmoys_maximal_fixed_vertex_planar_edge_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    exists K : SimpleGraph V,
      G <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      3 * Fintype.card V - 6 <= K.edgeSet.ncard := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.finite_planar_extension_maximal G hV hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.maximal_fixed_vertex_planar_edge_lower_bound K hV hK hmax⟩
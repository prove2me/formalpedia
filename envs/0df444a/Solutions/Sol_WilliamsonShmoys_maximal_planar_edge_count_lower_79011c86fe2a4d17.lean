-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_79011c86fe2a4d17
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:23:12.230351+00:00
-- url     : https://prove2.me/submissions/1bdabffc-57a5-42a1-b819-50d7efad1047
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_fixed_vertex_0e6cbe52_e2e3_41cf_80dc_2d34dacc7938

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V, U ≤ W →
      WilliamsonShmoys.HasPlanarDrawingOn W → W = U) :
    3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by
  obtain ⟨W, hUW, hW, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_fixed_vertex_0e6cbe52_e2e3_41cf_80dc_2d34dacc7938 U hV hU
  have hWU : W = U := hmax W hUW hW
  rw [hWU] at hcount
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_repair_543ac5d4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:44:26.69582+00:00
-- url     : https://prove2.me/submissions/ec0588ec-5e34-4994-9733-bebb1ad94fa1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_repair_543ac5d4
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_repair_543ac5d4

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T <= U →
      WilliamsonShmoys.HasPlanarDrawingOn U →
      U.edgeSet.ncard <= T.edgeSet.ncard) :
    3 * Fintype.card V = T.edgeSet.ncard + 6 := by
  obtain ⟨U, hTU, hU, hUeq⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_repair_543ac5d4 T hV hT
  have hmaxU := hmax U hTU hU
  have hbound :=
    WilliamsonShmoys.planar_edge_count_upper_bound_repair_543ac5d4 T hV hT
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_c61b3391
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:55:43.422988+00:00
-- url     : https://prove2.me/submissions/994f619f-97c9-445b-9808-5acdca64b51d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_extension_c61b3391

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hKmax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hKT, hT, hTcard⟩ :=
    WilliamsonShmoys.exists_planar_edge_count_extension_c61b3391 K hV hK
  have hTK : T <= K := hKmax T hKT hT
  have hEq : K = T := le_antisymm hKT hTK
  simpa [hEq] using hTcard
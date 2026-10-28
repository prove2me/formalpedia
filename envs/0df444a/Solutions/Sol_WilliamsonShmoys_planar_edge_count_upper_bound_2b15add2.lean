-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_2b15add2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:38:27.656361+00:00
-- url     : https://prove2.me/submissions/e52b3d35-86e0-472d-b105-449c9b0dbdae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulation_extension_for_edge_bound
import Theorems.Thm_WilliamsonShmoys_edge_count_mono
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hLH, _hHplanar, hHcount⟩ :=
    WilliamsonShmoys.exists_triangulation_extension_for_edge_bound L hV hL
  have hcount := WilliamsonShmoys.edge_count_mono L H hLH
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_fixed_vertex_type
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:15:20.171451+00:00
-- url     : https://prove2.me/submissions/0cbfbc98-bfad-4ae1-95b8-713dc614691e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_of_sparse

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ G : SimpleGraph V, H <= G → WilliamsonShmoys.HasPlanarDrawingOn G → G = H) :
    3 * Fintype.card V - 6 <= H.edgeSet.ncard := by
  by_contra hbound
  have hsparse : H.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
  obtain ⟨G, hHG, hneq, hG⟩ :=
    WilliamsonShmoys.planar_edge_augmentation_of_sparse H hV hH hsparse
  exact hneq (hmax G hHG hG)
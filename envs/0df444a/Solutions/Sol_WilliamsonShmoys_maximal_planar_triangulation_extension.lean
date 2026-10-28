-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:17:29.636661+00:00
-- url     : https://prove2.me/submissions/7f9bbd4b-f6cc-407b-a88b-28a7aa887030
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_extension_279755a6_02cd_4483_9b65_417cbe6cd492
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_279755a6_02cd_4483_9b65_417cbe6cd492

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    exists K : SimpleGraph V,
      H <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_drawingOn_extension_279755a6_02cd_4483_9b65_417cbe6cd492 H hH
  have hcount := WilliamsonShmoys.maximal_planar_drawingOn_edge_count_279755a6_02cd_4483_9b65_417cbe6cd492
    K hV hK hmax
  exact ⟨K, hHK, hK, hcount⟩
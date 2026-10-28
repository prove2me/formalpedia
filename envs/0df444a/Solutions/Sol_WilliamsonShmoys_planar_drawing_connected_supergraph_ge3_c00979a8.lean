-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_ge3_c00979a8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:25:46.893547+00:00
-- url     : https://prove2.me/submissions/7b880e2c-6de6-4ece-a715-b072e2b92fc8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_c00979a8
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_connected_ge3_c00979a8

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V => K <= H /\ H.Connected /\
      WilliamsonShmoys.HasPlanarDrawingOn H /\
      K.edgeSet.ncard <= H.edgeSet.ncard := by
  obtain ⟨H, hKH, hH, hmax, hcard⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_c00979a8 K hK
  exact ⟨H, hKH,
    WilliamsonShmoys.maximal_planar_supergraph_connected_ge3_c00979a8 H hV hH hmax,
    hH, hcard⟩
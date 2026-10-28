-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_connected_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:13:55.350997+00:00
-- url     : https://prove2.me/submissions/52e0fefd-138e-43eb-a65f-451562d6a3bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      J <= K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  obtain ⟨K, hJK, hDrawK, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count J hDraw
  exact ⟨K, hJK,
    WilliamsonShmoys.maximal_planar_supergraph_connected K hDrawK hMax hCard,
    hDrawK⟩
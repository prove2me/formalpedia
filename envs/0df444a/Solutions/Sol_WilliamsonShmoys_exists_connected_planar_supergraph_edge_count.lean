-- Prove2me | solution 1 for WilliamsonShmoys.exists_connected_planar_supergraph_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:52:18.74469+00:00
-- url     : https://prove2.me/submissions/2604cdd5-f53d-4b1d-925d-e86afab35e0e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_augmentation
import Theorems.Thm_WilliamsonShmoys_exists_connected_extension_of_local_augmentation

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ Y : SimpleGraph V,
      X.edgeSet.ncard ≤ Y.edgeSet.ncard ∧
      Y.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn Y := by
  exact WilliamsonShmoys.exists_connected_extension_of_local_augmentation
    X WilliamsonShmoys.HasPlanarDrawingOn hdraw
    (fun G _ hG hNotConnected =>
      WilliamsonShmoys.exists_planar_edge_augmentation G hG hCard hNotConnected)
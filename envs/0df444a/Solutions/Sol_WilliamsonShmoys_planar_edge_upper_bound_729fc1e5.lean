-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_729fc1e5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:37:07.845219+00:00
-- url     : https://prove2.me/submissions/f85b589c-532f-4ffd-8811-7e1a8c4ad785
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connectivity_augmentation_c3c27980_9f1d_4b26_ac26_4100a7115914
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound_c3c27980_9f1d_4b26_ac26_4100a7115914

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    R.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨S, hRS, hSconn, hSplanar⟩ :=
    WilliamsonShmoys.planar_connectivity_augmentation_c3c27980_9f1d_4b26_ac26_4100a7115914 R hR
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_upper_bound_c3c27980_9f1d_4b26_ac26_4100a7115914
      S hV hSconn hSplanar
  calc
    R.edgeSet.ncard ≤ S.edgeSet.ncard := hRS
    _ ≤ 3 * Fintype.card V - 6 := hbound
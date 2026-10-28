-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation_with_three_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:08:23.380914+00:00
-- url     : https://prove2.me/submissions/77414f02-7ae1-4615-a9dd-ca6dc12e8fec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  obtain ⟨K, hHK, hconn, hplanar⟩ :=
    WilliamsonShmoys.exists_connected_planar_supergraph H hH hV
  refine ⟨K, hHK, hconn, hplanar, ?_⟩
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hHK)
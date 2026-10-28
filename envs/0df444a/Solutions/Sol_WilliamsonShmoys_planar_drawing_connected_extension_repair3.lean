-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_repair3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:24:27.428183+00:00
-- url     : https://prove2.me/submissions/57c81095-c58b-4e8f-81a5-d6887b82b200
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_core

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V,
      T ≤ S ∧ HasPlanarDrawingOn S ∧ S.Connected ∧
      T.edgeSet.ncard ≤ S.edgeSet.ncard := by
  obtain ⟨S, hTS, hSPlanar, hSConnected⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_core T hT hCard
  refine ⟨S, hTS, hSPlanar, hSConnected, ?_⟩
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hTS)
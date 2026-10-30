-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_supergraph_connected__p2m_7cfe8adb_3896_4a89_9953_f0bd38318921_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:56:48.798012+00:00
-- url     : https://prove2.me/submissions/fdace24e-4304-43ba-8e2d-f269b2b8db7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph__p2m_304864e8_bb51_44c5_aa36_393fdd5ea875_a1
import Theorems.Thm_WilliamsonShmoys_connected_of_maximal_planar_drawing__p2m_304864e8_bb51_44c5_aa36_393fdd5ea875_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V, X.edgeSet ⊆ Y.edgeSet ∧ Y.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn Y := by
  obtain ⟨Y, hXY, hY, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_supergraph__p2m_304864e8_bb51_44c5_aa36_393fdd5ea875_a1 X hX
  exact ⟨Y, hXY,
    WilliamsonShmoys.connected_of_maximal_planar_drawing__p2m_304864e8_bb51_44c5_aa36_393fdd5ea875_a1 Y hY hmax,
    hY⟩
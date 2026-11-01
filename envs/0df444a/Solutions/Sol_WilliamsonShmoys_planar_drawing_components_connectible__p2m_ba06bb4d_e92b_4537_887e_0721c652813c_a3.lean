-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_components_connectible__p2m_ba06bb4d_e92b_4537_887e_0721c652813c_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:14:12.776824+00:00
-- url     : https://prove2.me/submissions/cb4f5dd1-28a0-4684-a359-9828073cb687
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard <= K.edgeSet.ncard := by
  obtain ⟨K, hHK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
      H hH
  exact ⟨K, hHK,
    WilliamsonShmoys.maximal_planar_drawing_connected__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
      K hcard hKplanar hKmax,
    hKplanar,
    WilliamsonShmoys.edgeSet_ncard_mono__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
      H K hHK⟩
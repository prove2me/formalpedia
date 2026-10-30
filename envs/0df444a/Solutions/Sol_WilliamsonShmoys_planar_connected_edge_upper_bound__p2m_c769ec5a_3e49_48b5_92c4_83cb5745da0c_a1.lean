-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_upper_bound__p2m_c769ec5a_3e49_48b5_92c4_83cb5745da0c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:23:00.366127+00:00
-- url     : https://prove2.me/submissions/4982833c-5209-4b54-a687-c1b5d5f9b097
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hConnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hKmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
      H hH
  have hKcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
      K hK hKmax hV
  have hmono :=
    WilliamsonShmoys.edgeSet_ncard_mono__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
      H K hHK
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_517c01cd_00fc_45c6_9fdb_091b579590d9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:03:51.491984+00:00
-- url     : https://prove2.me/submissions/14ec5419-92b5-4ba1-bb66-a5b13604e607

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_9bfb6b72_08dc_4057_9f94_78efbb45a4ca_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9bfb6b72_08dc_4057_9f94_78efbb45a4ca_a1
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_9bfb6b72_08dc_4057_9f94_78efbb45a4ca_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9bfb6b72_08dc_4057_9f94_78efbb45a4ca_a1 K hK
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_9bfb6b72_08dc_4057_9f94_78efbb45a4ca_a1 H hH hV hmax
  have hmono :=
    WilliamsonShmoys.edgeSet_ncard_mono__p2m_9bfb6b72_08dc_4057_9f94_78efbb45a4ca_a1 K H hKH
  omega
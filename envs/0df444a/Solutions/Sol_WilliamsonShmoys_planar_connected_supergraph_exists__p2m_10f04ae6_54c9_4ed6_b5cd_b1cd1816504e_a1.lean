-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph_exists__p2m_10f04ae6_54c9_4ed6_b5cd_b1cd1816504e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:46:56.471314+00:00
-- url     : https://prove2.me/submissions/d72b563d-4914-43fc-99f2-0e9cc3ee91f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_completion_from_edge_step__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  classical
  exact WilliamsonShmoys.planar_connected_completion_from_edge_step__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a2
    (P := WilliamsonShmoys.HasPlanarDrawingOn) H hH
    (fun G hG hn => WilliamsonShmoys.planar_drawing_add_bridge__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a2 G hG hn)
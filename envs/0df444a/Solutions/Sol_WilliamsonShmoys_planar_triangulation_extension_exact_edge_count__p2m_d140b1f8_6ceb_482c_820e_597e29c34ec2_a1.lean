-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_exact_edge_count__p2m_d140b1f8_6ceb_482c_820e_597e29c34ec2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T20:08:32.9343+00:00
-- url     : https://prove2.me/submissions/aaf1e2bf-e6ed-46db-a2e1-449a1725071f

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_0d3ba6cc_be4a_436c_b614_289a3ecc8076_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_triangulation_completion__p2m_0d3ba6cc_be4a_436c_b614_289a3ecc8076_a1 K hK hcard
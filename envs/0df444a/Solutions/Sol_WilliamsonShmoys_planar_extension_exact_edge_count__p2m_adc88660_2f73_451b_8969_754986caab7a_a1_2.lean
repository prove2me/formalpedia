-- Prove2me | solution 2 for WilliamsonShmoys.planar_extension_exact_edge_count__p2m_adc88660_2f73_451b_8969_754986caab7a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:42:15.303645+00:00
-- url     : https://prove2.me/submissions/99fad160-ce51-4b65-9d28-0aa5e33b5bf1

import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_completion

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_graph_has_triangulation_completion N hV hN

-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_upper_bound_of_components__p2m_d428652f_4806_46f7_95cc_5b75c77bec4b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:00:09.485202+00:00
-- url     : https://prove2.me/submissions/d4cc65ab-ea96-4f2d-861a-5055eb3d96e5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_statistics__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a2
import Theorems.Thm_WilliamsonShmoys_component_arithmetic__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hconnected : ∀ {U : Type} [Fintype U] [LinearOrder U]
      (N : SimpleGraph U) (dN : DecidableRel N.Adj),
      HasPlanarDrawingOn N → N.Connected → 3 ≤ Fintype.card U →
      N.edgeFinset.card ≤ 3 * Fintype.card U - 6)
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨parts, hvertices, hedges, hparts⟩ :=
    WilliamsonShmoys.component_statistics__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a2
      hconnected M dM hM
  exact WilliamsonShmoys.component_arithmetic__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a2
    (Fintype.card V) (M.edgeFinset.card) parts hvertices hedges hparts hcard
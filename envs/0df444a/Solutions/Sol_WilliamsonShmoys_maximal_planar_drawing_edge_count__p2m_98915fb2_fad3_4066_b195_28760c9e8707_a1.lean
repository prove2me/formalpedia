-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_98915fb2_fad3_4066_b195_28760c9e8707_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:41:24.990906+00:00
-- url     : https://prove2.me/submissions/55038854-16ba-438a-92b0-15940c9c0a73

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_d2e6787a_41a9_4272_bec1_4c170f4b8b09_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ S : SimpleGraph V, R ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S → S = R) :
    (letI : DecidableRel R.Adj := Classical.decRel R.Adj
     R.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨S, hRS, hS, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_d2e6787a_41a9_4272_bec1_4c170f4b8b09_a1
      R hR hcard
  have hSR : S = R := hmax S hRS hS
  subst S
  exact hcount
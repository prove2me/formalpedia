-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:27:04.707749+00:00
-- url     : https://prove2.me/submissions/af5bffe3-9c0f-445f-990a-758cadd7662b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_ec87f3de_339b_432c_a6c1_ac3963609395_a1

set_option autoImplicit false
theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ Q : SimpleGraph V, N.edgeSet ⊆ Q.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn Q → Q.edgeSet = N.edgeSet) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Q, hsub, hQdraw, hQcard⟩ :=
    WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_ec87f3de_339b_432c_a6c1_ac3963609395_a1 N hV hDraw
  have hEq := hmax Q hsub hQdraw
  rw [← hEq]
  exact hQcard
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_dc9018d8_e47b_47c1_8eef_84ccb4273562_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:05:52.797983+00:00
-- url     : https://prove2.me/submissions/f3e1bd85-134e-47ec-b516-29893ef1bb31

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_73871160_1692_421c_aaf6_a7b2b6384c07_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = T.edgeSet.ncard + 2 ∧
      3 * f = 2 * T.edgeSet.ncard := by
  have hm : T.edgeSet.ncard + 6 = 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_73871160_1692_421c_aaf6_a7b2b6384c07_a1
      T hT hmax hV
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega
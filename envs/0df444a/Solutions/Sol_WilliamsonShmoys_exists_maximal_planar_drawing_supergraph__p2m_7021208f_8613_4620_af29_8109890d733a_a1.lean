-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_drawing_supergraph__p2m_7021208f_8613_4620_af29_8109890d733a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:36:36.582251+00:00
-- url     : https://prove2.me/submissions/1dc1e2cc-ddd9-4692-837e-b7de5f21a05d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_order_maximal_extension__p2m_5c7296d8_cb4f_4c5c_9e1f_d382ba5a4bb4_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      S ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by
  classical
  obtain ⟨T, hST, hT, hmax⟩ :=
    WilliamsonShmoys.finite_order_maximal_extension__p2m_5c7296d8_cb4f_4c5c_9e1f_d382ba5a4bb4_a1
      (α := SimpleGraph V)
      (P := fun G => S ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
      (x := S) ⟨le_rfl, hS⟩
  refine ⟨T, hST, hT.2, ?_⟩
  intro U hTU hU
  exact hmax U hTU ⟨le_trans hST hTU, hU⟩
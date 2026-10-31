-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:46:33.162402+00:00
-- url     : https://prove2.me/submissions/71747c66-c43f-412e-9084-0e24875ea170

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_36d62909_fefb_443f_ad8e_654ce0b0b7dd_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_if_sparse__p2m_36d62909_fefb_443f_ad8e_654ce0b0b7dd_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper__p2m_36d62909_fefb_443f_ad8e_654ce0b0b7dd_a2
      K hK hV
  have hNotSparse : ¬ K.edgeSet.ncard + 6 < 3 * Fintype.card V := by
    intro hSparse
    obtain ⟨L, hKL, hneq, hL⟩ :=
      WilliamsonShmoys.planar_edge_augmentation_if_sparse__p2m_36d62909_fefb_443f_ad8e_654ce0b0b7dd_a2
        K hK hV hSparse
    exact hneq (hmax L hKL hL)
  omega
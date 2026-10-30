-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_648e2563_4933_48d5_af68_a43e4e82ab0d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:30:32.553264+00:00
-- url     : https://prove2.me/submissions/56100c73-59d6-4975-bba6-914ae0df6cee

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_bound__p2m_6d943741_fae6_4c58_9301_d8625eecfd1e_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  by_contra h
  have hlt : K.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨L, hKL, hL⟩ :=
    WilliamsonShmoys.planar_edge_augmentation_below_bound__p2m_6d943741_fae6_4c58_9301_d8625eecfd1e_a1
      K hK hV hlt
  exact hKL.ne (hKmax L (le_of_lt hKL) hL).symm
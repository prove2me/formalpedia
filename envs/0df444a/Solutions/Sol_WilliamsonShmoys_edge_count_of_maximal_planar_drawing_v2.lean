-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:47:03.200099+00:00
-- url     : https://prove2.me/submissions/2bdb53f1-8498-42a6-a266-06bbb83c3f96

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_v2
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_when_sparse_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V, Q ≤ R →
      WilliamsonShmoys.HasPlanarDrawingOn R → R = Q) :
    3 * Fintype.card V - 6 = Q.edgeSet.ncard := by
  have hup := WilliamsonShmoys.planar_edge_count_upper_bound_v2 Q hV hQ
  have hnot : ¬ Q.edgeSet.ncard < 3 * Fintype.card V - 6 := by
    intro hsmall
    obtain ⟨R, hQR, hneq, hR⟩ :=
      WilliamsonShmoys.planar_augmentation_when_sparse_v2 Q hV hQ hsmall
    exact hneq (hmax R hQR hR)
  omega
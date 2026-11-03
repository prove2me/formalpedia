-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_triangulated_supergraph__p2m_cf161613_a0bb_4259_95d5_c320f30b7319_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:24:42.103207+00:00
-- url     : https://prove2.me/submissions/b281ae55-add6-4151-8034-a078db40c3ce

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximum_drawable_supergraph__p2m_14ab409d_ba46_4520_b2b1_fae32ccc2155_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count__p2m_14ab409d_ba46_4520_b2b1_fae32ccc2155_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_maximum_drawable_supergraph__p2m_14ab409d_ba46_4520_b2b1_fae32ccc2155_a1
      M hM
  have hmaxN : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ N.edgeSet.ncard := by
    intro K hNK hK
    exact hmax K (le_trans hMN hNK) hK
  have hcount :=
    WilliamsonShmoys.maximal_drawable_supergraph_edge_count__p2m_14ab409d_ba46_4520_b2b1_fae32ccc2155_a1
      M N hMN hN hCard hmaxN
  exact ⟨N, hMN, hN, hcount⟩
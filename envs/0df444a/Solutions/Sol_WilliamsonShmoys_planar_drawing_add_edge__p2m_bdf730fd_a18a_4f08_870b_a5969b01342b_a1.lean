-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:30:35.265381+00:00
-- url     : https://prove2.me/submissions/bde2fba6-1385-40fb-a166-c3efdfa7414e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_add_one_edge__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hGap : M.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = M.edgeSet.ncard + 1 := by
  obtain ⟨N, hMN, hDrawN, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
      M hDraw
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
      N hV hDrawN hmax
  have hlt : M.edgeSet.ncard < N.edgeSet.ncard := by
    rw [hcount]
    omega
  exact WilliamsonShmoys.planar_supergraph_add_one_edge__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
    M N hMN hDraw hDrawN hlt
-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_max_pair_count__p2m_bb57e846_d9a4_493d_944c_0498086a1fa4_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:25:21.864605+00:00
-- url     : https://prove2.me/submissions/fd295d57-439b-4591-bfd0-ac7bef969dce

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximizer_of_bounded__p2m_6dfe235c_2d93_4cd3_a1e8_c2011cbaaa57_a1
import Theorems.Thm_WilliamsonShmoys_ordered_adj_card_le_universe__p2m_6dfe235c_2d93_4cd3_a1e8_c2011cbaaa57_a1

set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ L : SimpleGraph V, H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
        Nat.card {p : V × V // M.Adj p.1 p.2} ≤
          Nat.card {p : V × V // L.Adj p.1 p.2} := by
  obtain ⟨L, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximizer_of_bounded__p2m_6dfe235c_2d93_4cd3_a1e8_c2011cbaaa57_a1
      (P := fun G : SimpleGraph V => H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
      (f := fun G => Nat.card {p : V × V // G.Adj p.1 p.2})
      ⟨H, le_rfl, hDraw⟩ (Nat.card (V × V))
      (by
        intro G hG
        exact WilliamsonShmoys.ordered_adj_card_le_universe__p2m_6dfe235c_2d93_4cd3_a1e8_c2011cbaaa57_a1 G)
  exact ⟨L, hL.1, hL.2, fun M hHM hDrawM => hmax M ⟨hHM, hDrawM⟩⟩
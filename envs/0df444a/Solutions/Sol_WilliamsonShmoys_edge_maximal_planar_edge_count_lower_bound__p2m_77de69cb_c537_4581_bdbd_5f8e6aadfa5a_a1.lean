-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound__p2m_77de69cb_c537_4581_bdbd_5f8e6aadfa5a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:57:12.184157+00:00
-- url     : https://prove2.me/submissions/af6e9b32-d3c1-4614-b429-be8770010944
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_exact_edge_count__p2m_c45030e1_ea7d_4e8a_8e32_e5d647bd706c_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hmax : forall M : SimpleGraph V, G <= M -> HasPlanarDrawingOn M -> M = G) :
    3 * Fintype.card V - 6 <= G.edgeSet.ncard := by
  rcases WilliamsonShmoys.planar_extension_exact_edge_count__p2m_c45030e1_ea7d_4e8a_8e32_e5d647bd706c_a1
      G hV hG with ⟨M, hGM, hM, hcount⟩
  have hMG : M = G := hmax M hGM hM
  rw [hMG] at hcount
  exact Nat.le_of_eq hcount.symm
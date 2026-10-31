-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_triangle_count__p2m_2a0eb6c3_e8b8_46c5_bb28_c648f00dcb7f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:18:31.536996+00:00
-- url     : https://prove2.me/submissions/c4d8efeb-41e4-4789-be1a-9e37940315ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_17eb0fc8_3683_4688_9bd5_07f26a4d1b81_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_17eb0fc8_3683_4688_9bd5_07f26a4d1b81_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  have hm_lower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_17eb0fc8_3683_4688_9bd5_07f26a4d1b81_a1
    (V := V) K hV hK hmax
  have hm_upper := WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_17eb0fc8_3683_4688_9bd5_07f26a4d1b81_a1
    (V := V) K hV hK
  have hm : K.edgeSet.ncard = 3 * (Fintype.card V - 2) := Nat.le_antisymm hm_upper hm_lower
  refine ⟨2 * (Fintype.card V - 2), ?_, ?_⟩
  · rw [hm]
    omega
  · rw [hm]
    omega
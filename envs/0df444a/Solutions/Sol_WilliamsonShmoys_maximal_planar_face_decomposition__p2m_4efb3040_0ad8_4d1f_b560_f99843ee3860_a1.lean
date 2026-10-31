-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_4efb3040_0ad8_4d1f_b560_f99843ee3860_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:41:39.235725+00:00
-- url     : https://prove2.me/submissions/18c0f59f-bde1-4d38-85f4-9f04ddbd5571

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_2e1bfcb4_daf5_4b6a_9257_36b9f3fd3710_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_2e1bfcb4_daf5_4b6a_9257_36b9f3fd3710_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hMax : ∀ N : SimpleGraph V, G ≤ N → HasPlanarDrawingOn N → N = G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f = 2 * G.edgeSet.ncard := by
  let n := Fintype.card V
  let e := G.edgeSet.ncard
  have hUpper : e + 6 ≤ 3 * n :=
    WilliamsonShmoys.planar_edge_upper_bound__p2m_2e1bfcb4_daf5_4b6a_9257_36b9f3fd3710_a2 G hG hCard
  have hLower : 3 * n ≤ e + 6 :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_2e1bfcb4_daf5_4b6a_9257_36b9f3fd3710_a2 G hG hMax hCard
  have hExact : e + 6 = 3 * n := Nat.le_antisymm hUpper hLower
  refine ⟨2 * n - 4, ?_, ?_⟩ <;> dsimp [n, e] at hExact ⊢ <;> omega
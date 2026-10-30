-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_26cbec15_a016_4bbf_b55b_721eefe9b1c1_a6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:58:58.490999+00:00
-- url     : https://prove2.me/submissions/4e76e4ec-acb4-48bc-962b-e0216600ebbe

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_dc18341a_a219_427c_98ac_62a72970a5ea_a6
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_dc18341a_a219_427c_98ac_62a72970a5ea_a6

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, Set.Subset L.edgeSet M.edgeSet →
      HasPlanarDrawingOn M → Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  have hUpper := WilliamsonShmoys.planar_edge_upper_bound__p2m_dc18341a_a219_427c_98ac_62a72970a5ea_a6 L hL hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_dc18341a_a219_427c_98ac_62a72970a5ea_a6 L hL hMax hCard
  have hEdge : L.edgeSet.ncard + 6 = 3 * Fintype.card V := Nat.le_antisymm hUpper hLower
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega
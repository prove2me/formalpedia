-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_dc18341a_a219_427c_98ac_62a72970a5ea_a6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:15:39.154287+00:00
-- url     : https://prove2.me/submissions/312f7da0-9b14-45c3-a6fc-45f333666399

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_cardinality__p2m_e15f7e2c_ce0e_4996_9963_e731b96f551d_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, Set.Subset L.edgeSet M.edgeSet →
      HasPlanarDrawingOn M → Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hM, hMcard⟩ :=
    WilliamsonShmoys.planar_completion_cardinality__p2m_e15f7e2c_ce0e_4996_9963_e731b96f551d_a1
      L hL hCard
  have hML : Set.Subset M.edgeSet L.edgeSet := hMax M hLM hM
  have hEq : L.edgeSet = M.edgeSet := Set.Subset.antisymm hLM hML
  have hcount : L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    simpa [hEq] using hMcard
  omega
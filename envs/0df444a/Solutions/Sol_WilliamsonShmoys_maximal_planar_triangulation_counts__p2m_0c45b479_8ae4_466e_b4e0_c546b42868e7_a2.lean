-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_counts__p2m_0c45b479_8ae4_466e_b4e0_c546b42868e7_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:19:43.458211+00:00
-- url     : https://prove2.me/submissions/78459e98-21f1-4aa7-b641-6cb9a6b5d541
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_3b0cc7ba_e438_41c2_b251_7b0cfc52f510_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_3b0cc7ba_e438_41c2_b251_7b0cfc52f510_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      ∃ f : ℕ,
        L.edgeFinset.card + 2 = Fintype.card V + f ∧
        3 * f = 2 * L.edgeFinset.card) := by
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  have hup := WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_3b0cc7ba_e438_41c2_b251_7b0cfc52f510_a1 L hL hcard
  have hlo := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_3b0cc7ba_e438_41c2_b251_7b0cfc52f510_a1 L hL hcard hmax
  have he : L.edgeFinset.card + 6 = 3 * Fintype.card V := Nat.le_antisymm hup hlo
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega
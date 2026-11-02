-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_535e4e7e_28ad_48ed_9188_305d88c71848_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:01:32.285688+00:00
-- url     : https://prove2.me/submissions/46b70d18-0013-4c55-bbe4-dc09572cdab0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count__p2m_3b189e66_afee_4feb_9bd4_e20d54522d03_a3
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    3 * Fintype.card V ≤ L.edgeFinset.card + 6 := by
  classical
  obtain ⟨M, hLM, hM, hEdges⟩ :=
    WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_3b189e66_afee_4feb_9bd4_e20d54522d03_a3 L hV hL
  have hML : M ≤ L := hmax M hLM hM
  have hEq : L = M := le_antisymm hLM hML
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  change M.edgeFinset.card = 3 * Fintype.card V - 6 at hEdges
  rw [hEq]
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_055d45fa_a44d_4012_991d_80fcbbc5becb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:32:36.877187+00:00
-- url     : https://prove2.me/submissions/7d4be79e-3baa-4fee-9889-30213f6a3beb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_completion__p2m_5ea12a57_b3bb_4923_a983_804aaa92fdce_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      3 * Fintype.card V ≤ L.edgeFinset.card + 6) := by
  classical
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨M, hLM, hM, htri⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulation_completion__p2m_5ea12a57_b3bb_4923_a983_804aaa92fdce_a1
      L hL hcard
  have hML : M ≤ L := hmax M hLM hM
  have hEq : M = L := le_antisymm hML hLM
  rw [hEq] at htri
  exact htri.le
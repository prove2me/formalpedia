-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_graph_6230202c_e2d1_4f54_a7eb_9eadc154ee57
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:23:11.182333+00:00
-- url     : https://prove2.me/submissions/17fd653a-e278-402c-b877-d9c2adc14570
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_2026
import Theorems.Thm_WilliamsonShmoys_planar_strict_extension_below_bound_2026

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, L ≤ K → HasPlanarDrawingOn K → K = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hbound := WilliamsonShmoys.planar_simple_graph_edge_bound_2026 L hL hCard
  by_contra hne
  have hstrict : L.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨K, hLK, hK, hKL⟩ :=
    WilliamsonShmoys.planar_strict_extension_below_bound_2026
      L hL hCard hstrict
  exact hKL (hmax K hLK hK)
-- Prove2me | solution 1 for WilliamsonShmoys.efb0a43e_maximal_drawable_exact_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:20:21.698664+00:00
-- url     : https://prove2.me/submissions/fd181519-6d2a-47ab-909b-bbbebd900229
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound
import Theorems.Thm_WilliamsonShmoys_drawable_graph_can_be_extended

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hbound :=
    WilliamsonShmoys.planar_edge_count_bound K hK hCard
  by_contra hneq
  have hlt : K.edgeSet.ncard + 6 < 3 * Fintype.card V := by
    omega
  obtain ⟨L, hKL, hLK, hL⟩ :=
    WilliamsonShmoys.drawable_graph_can_be_extended K hK hCard hlt
  exact hLK (hmax L hKL hL)
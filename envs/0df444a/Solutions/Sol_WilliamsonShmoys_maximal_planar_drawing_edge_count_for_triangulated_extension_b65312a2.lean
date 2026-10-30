-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_for_triangulated_extension_b65312a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:14:11.527492+00:00
-- url     : https://prove2.me/submissions/3a579b44-b4c2-45f5-93e1-e01c32bc407b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_upper_bound_v3
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation_below_bound_v3
import Mathlib.Data.Set.Card
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hNdraw : HasPlanarDrawingOn N)
    (hNmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  have hup : N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound_v3 N hV hNdraw
  have hnotlt : ¬ N.edgeSet.ncard + 6 < 3 * Fintype.card V := by
    intro hlt
    obtain ⟨K, hNK, hKdraw, hstrict⟩ :=
      WilliamsonShmoys.planar_drawing_edge_augmentation_below_bound_v3
        N hV hNdraw hlt
    have hKN : K = N := hNmax K hNK hKdraw
    rw [hKN] at hstrict
    exact (Nat.lt_irrefl _ hstrict)
  omega
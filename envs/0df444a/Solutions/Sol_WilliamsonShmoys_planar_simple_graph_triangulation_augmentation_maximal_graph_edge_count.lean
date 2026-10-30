-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_triangulation_augmentation_maximal_graph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:27:09.236405+00:00
-- url     : https://prove2.me/submissions/377e044f-3a6a-4bd6-9d7f-80aa6f3918c0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_strict_extension_below_max_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  let b : Int := 3 * (Fintype.card V : Int) - 6
  have hup : (K.edgeSet.ncard : Int) ≤ b := by
    simpa [b] using
      WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound K hK hCard
  have hlo : b ≤ (K.edgeSet.ncard : Int) := by
    by_contra hnot
    have hlt : (K.edgeSet.ncard : Int) < b := lt_of_not_ge hnot
    obtain ⟨L, hstrict, hL⟩ :=
      WilliamsonShmoys.planar_drawing_has_strict_extension_below_max_edge_count
        K hK hCard (by simpa [b] using hlt)
    exact hMax L hstrict hL
  dsimp [b] at hup hlo ⊢
  omega
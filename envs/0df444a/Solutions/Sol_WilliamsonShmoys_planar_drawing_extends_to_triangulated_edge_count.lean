-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extends_to_triangulated_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:42:34.83591+00:00
-- url     : https://prove2.me/submissions/59490cc7-7e79-4e47-95b6-28db8cb5d78e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph_f3b6ee58
import Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_has_maximal_edge_count_f3b6ee58

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      L.edgeSet ⊆ K.edgeSet ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hK, hLK, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph_f3b6ee58
      (V := V) (L := L) hL
  refine ⟨K, hK, hLK, ?_⟩
  exact WilliamsonShmoys.inclusion_maximal_planar_has_maximal_edge_count_f3b6ee58
    (V := V) (K := K) hV hK hmax
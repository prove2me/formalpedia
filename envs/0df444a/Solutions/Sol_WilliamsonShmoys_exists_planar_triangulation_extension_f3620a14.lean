-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension_f3620a14
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:32:47.167239+00:00
-- url     : https://prove2.me/submissions/6b206f3e-7341-4e66-82c5-cf622c51d5c7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension_f3620a14
import Theorems.Thm_WilliamsonShmoys_edge_count_eq_of_maximal_planar_drawing_f3620a14

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      T ≤ S ∧
      S.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨S, hS, hTS, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_extension_f3620a14 T hT
  refine ⟨S, hS, hTS, ?_⟩
  exact WilliamsonShmoys.edge_count_eq_of_maximal_planar_drawing_f3620a14 S hS hCard hmax
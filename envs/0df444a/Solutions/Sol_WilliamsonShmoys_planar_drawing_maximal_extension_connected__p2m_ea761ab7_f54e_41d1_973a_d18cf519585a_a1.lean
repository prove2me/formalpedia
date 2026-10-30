-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_connected__p2m_ea761ab7_f54e_41d1_973a_d18cf519585a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T13:09:37.082701+00:00
-- url     : https://prove2.me/submissions/95dd6f09-6b95-4a82-8cf9-43e87f622bf9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_1a3fa5c0_9591_452f_a68f_799eb6d63bf3_a2
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    Exists fun K : SimpleGraph V =>
      And (Set.Subset H.edgeSet K.edgeSet)
        (And (WilliamsonShmoys.HasPlanarDrawingOn K)
          (And K.Connected
            (forall M : SimpleGraph V,
              Set.Subset K.edgeSet M.edgeSet ->
              WilliamsonShmoys.HasPlanarDrawingOn M ->
              Set.Subset M.edgeSet K.edgeSet))) := by
  rcases WilliamsonShmoys.planar_drawing_maximal_extension__p2m_1a3fa5c0_9591_452f_a68f_799eb6d63bf3_a2 H hH with ⟨K, hHK, hKdraw, hKmax⟩
  refine ⟨K, hHK, hKdraw, ?_, hKmax⟩
  exact hconn.mono (SimpleGraph.edgeSet_subset_edgeSet.mp hHK)
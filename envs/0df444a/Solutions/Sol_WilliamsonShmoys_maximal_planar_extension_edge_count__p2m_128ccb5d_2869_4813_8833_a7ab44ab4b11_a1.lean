-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_128ccb5d_2869_4813_8833_a7ab44ab4b11_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:23:28.339985+00:00
-- url     : https://prove2.me/submissions/b77448a3-5424-48db-8dbf-3d65e25124a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_8d45bf42_38ea_432e_b84b_d41270aef8ba_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_8d45bf42_38ea_432e_b84b_d41270aef8ba_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V) :
    Exists (fun H : SimpleGraph V =>
      And (W <= H) (And (HasPlanarDrawingOn H)
        (H.edgeSet.ncard = 3 * Fintype.card V - 6)) ) := by
  apply Exists.elim
    (WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_8d45bf42_38ea_432e_b84b_d41270aef8ba_a2 W hW)
  intro H hH
  exact Exists.intro H
    (And.intro hH.1 (And.intro hH.2.1
      (WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_8d45bf42_38ea_432e_b84b_d41270aef8ba_a2 H hV hH.2.1 hH.2.2)))
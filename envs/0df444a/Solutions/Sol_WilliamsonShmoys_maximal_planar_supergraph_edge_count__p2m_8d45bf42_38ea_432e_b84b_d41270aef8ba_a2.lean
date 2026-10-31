-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_8d45bf42_38ea_432e_b84b_d41270aef8ba_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:41:01.524027+00:00
-- url     : https://prove2.me/submissions/2848450e-82b3-47c5-a5f3-00327f8e3f9a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_08a17077_59d5_43fa_bc2a_526ccd70f8a2_a1
import Theorems.Thm_WilliamsonShmoys_planar_graph_augmentable_below_maximal_edge_count__p2m_08a17077_59d5_43fa_bc2a_526ccd70f8a2_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_08a17077_59d5_43fa_bc2a_526ccd70f8a2_a1
      H hV hH
  by_contra hnot
  have hbelow :
      H.edgeSet.ncard <
        3 * Fintype.card V - 6 :=
    Nat.lt_of_le_of_ne hupper hnot
  obtain ⟨K, hHK, hKH, hK⟩ :=
    WilliamsonShmoys.planar_graph_augmentable_below_maximal_edge_count__p2m_08a17077_59d5_43fa_bc2a_526ccd70f8a2_a1
      H hV hH hbelow
  exact hKH (hmax K hHK hK)
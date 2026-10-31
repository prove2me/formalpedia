-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_152d6993_7004_4697_ab26_f8c2f883dc25_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:42:09.581115+00:00
-- url     : https://prove2.me/submissions/c6729223-1fbc-407e-bd5b-c7ea8b8968a4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists__p2m_ba617e25_272f_480b_8c9f_e5a82d8e4502_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count__p2m_ba617e25_272f_480b_8c9f_e5a82d8e4502_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V, M ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧
      S.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨S, hMS, hS, hMax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_ba617e25_272f_480b_8c9f_e5a82d8e4502_a1
      M hM hCard
  have hCount :=
    WilliamsonShmoys.maximal_drawable_supergraph_edge_count__p2m_ba617e25_272f_480b_8c9f_e5a82d8e4502_a1
      S hS hCard hMax
  exact ⟨S, hMS, hS, hCount⟩
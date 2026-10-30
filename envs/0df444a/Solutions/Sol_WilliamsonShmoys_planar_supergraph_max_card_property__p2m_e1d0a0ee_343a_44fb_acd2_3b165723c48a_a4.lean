-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_max_card_property__p2m_e1d0a0ee_343a_44fb_acd2_3b165723c48a_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:19.298844+00:00
-- url     : https://prove2.me/submissions/35510d69-c0c4-4efc-9c27-60cc1c2355d3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_extension_max_card_exists__p2m_056354fe_8081_4e5e_ae62_0d709f8aad22_a1
import Theorems.Thm_WilliamsonShmoys_ordered_adj_card_eq_rigidity__p2m_056354fe_8081_4e5e_ae62_0d709f8aad22_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
        (Nat.card {p : V × V // L.Adj p.1 p.2} ≤
          Nat.card {p : V × V // K.Adj p.1 p.2}) ∧
        (Nat.card {p : V × V // L.Adj p.1 p.2} =
          Nat.card {p : V × V // K.Adj p.1 p.2} → L ≤ K) := by
  obtain ⟨K, hJK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_extension_max_card_exists__p2m_056354fe_8081_4e5e_ae62_0d709f8aad22_a1 J hJ
  refine ⟨K, hJK, hK, ?_⟩
  intro L hKL hL
  constructor
  · exact hmax L hKL hL
  · intro hcard
    exact WilliamsonShmoys.ordered_adj_card_eq_rigidity__p2m_056354fe_8081_4e5e_ae62_0d709f8aad22_a1 K L hKL hcard
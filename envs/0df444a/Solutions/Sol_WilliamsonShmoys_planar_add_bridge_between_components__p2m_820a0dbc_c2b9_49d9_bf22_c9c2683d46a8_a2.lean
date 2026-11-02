-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_bridge_between_components__p2m_820a0dbc_c2b9_49d9_bf22_c9c2683d46a8_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:47:07.592278+00:00
-- url     : https://prove2.me/submissions/b883931b-3a5d-4da4-9a2b-f460ed56f489
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_graph_has_unreachable_pair__p2m_a01887ab_b605_44b6_af24_b6696d8b1f6b_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_unreachable_vertices__p2m_a01887ab_b605_44b6_af24_b6696d8b1f6b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) (hdis : ¬ K.Connected) :
    ∃ a b : V, a ≠ b ∧ ¬ K.Adj a b ∧
      ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ L.Adj a b ∧
        ∀ u v, L.Adj u v →
          K.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  obtain ⟨a, b, hab, hnotAdj, hnotReach⟩ :=
    WilliamsonShmoys.disconnected_graph_has_unreachable_pair__p2m_a01887ab_b605_44b6_af24_b6696d8b1f6b_a1
      K hcard hdis
  obtain ⟨L, hKL, hL, hLab, honly⟩ :=
    WilliamsonShmoys.planar_drawing_add_edge_between_unreachable_vertices__p2m_a01887ab_b605_44b6_af24_b6696d8b1f6b_a1
      K a b hnotReach hK
  exact ⟨a, b, hab, hnotAdj, L, hKL, hL, hLab, honly⟩
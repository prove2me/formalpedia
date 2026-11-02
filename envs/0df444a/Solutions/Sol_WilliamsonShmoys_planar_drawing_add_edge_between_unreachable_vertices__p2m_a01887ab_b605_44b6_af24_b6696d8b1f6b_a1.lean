-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_between_unreachable_vertices__p2m_a01887ab_b605_44b6_af24_b6696d8b1f6b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:06:07.595169+00:00
-- url     : https://prove2.me/submissions/32df2765-0afa-44a1-aadc-b048d4e62452
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_unreachable_vertices_component_cut__p2m_95b2a4a5_f4af_45e5_83a3_0810e97a8978_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_across_cut__p2m_95b2a4a5_f4af_45e5_83a3_0810e97a8978_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (a b : V)
    (hnotReach : ¬ K.Reachable a b)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ L.Adj a b ∧
      ∀ u v, L.Adj u v →
        K.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  obtain ⟨P, ha, hb, hcut⟩ :=
    WilliamsonShmoys.planar_unreachable_vertices_component_cut__p2m_95b2a4a5_f4af_45e5_83a3_0810e97a8978_a2
      K a b hnotReach
  exact WilliamsonShmoys.planar_drawing_add_edge_across_cut__p2m_95b2a4a5_f4af_45e5_83a3_0810e97a8978_a2
    K P a b ha hb hcut hK
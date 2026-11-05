-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_bridge_iteration__p2m_6542605d_05b7_4349_89df_2d6e0eb6b2d4_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:03:05.701892+00:00
-- url     : https://prove2.me/submissions/46ddf4a0-2bdd-4b8f-946e-d76e52c0a060

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_bridge_extension__p2m_5d530b65_2a84_4113_95c6_4b4a03a3063e_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    (hstep : ∀ (K : SimpleGraph V),
      G.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K →
      ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet ∧
        (∃ u v, ¬ K.Reachable u v ∧ L.Adj u v) ∧
        HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.exists_connected_supergraph_of_bridge_extension__p2m_5d530b65_2a84_4113_95c6_4b4a03a3063e_a1
    G HasPlanarDrawingOn hplanar hstep
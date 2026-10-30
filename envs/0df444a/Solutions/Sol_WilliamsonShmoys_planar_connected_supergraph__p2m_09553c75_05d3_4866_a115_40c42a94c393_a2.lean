-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph__p2m_09553c75_05d3_4866_a115_40c42a94c393_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:36:56.972992+00:00
-- url     : https://prove2.me/submissions/b8d663ff-8b58-4ed9-89d0-84568ed7722e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_component_bridge__p2m_ce6f5f96_18b4_457b_8f01_9dcd9d3bda8a_a1
import Theorems.Thm_WilliamsonShmoys_finite_planar_bridge_iteration__p2m_ce6f5f96_18b4_457b_8f01_9dcd9d3bda8a_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ H : SimpleGraph V,
      H.Connected ∧
      (∀ ⦃u v : V⦄, U.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      U.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  have hStep :
      ∀ K : SimpleGraph V, U ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → ¬ K.Connected →
        ∃ L : SimpleGraph V,
          K ≤ L ∧ K.edgeSet ⊂ L.edgeSet ∧
          WilliamsonShmoys.HasPlanarDrawingOn L := by
    intro K hUK hK hDisconnected
    exact WilliamsonShmoys.planar_component_bridge__p2m_ce6f5f96_18b4_457b_8f01_9dcd9d3bda8a_a1
      K hV hK hDisconnected
  obtain ⟨H, hUH, hConnected, hH, hEdgeCount⟩ :=
    WilliamsonShmoys.finite_planar_bridge_iteration__p2m_ce6f5f96_18b4_457b_8f01_9dcd9d3bda8a_a1
      U hU hStep
  exact ⟨H, hConnected, hUH, hH, hEdgeCount⟩
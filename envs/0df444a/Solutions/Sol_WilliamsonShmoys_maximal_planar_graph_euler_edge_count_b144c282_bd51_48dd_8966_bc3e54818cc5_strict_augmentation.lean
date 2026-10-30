-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5_strict_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:45:07.06333+00:00
-- url     : https://prove2.me/submissions/cf4f2185-46cc-477d-a494-290aeb2791eb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_euler_count

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hsparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeSet ⊆ M.edgeSet ∧
      ¬ M.edgeSet ⊆ L.edgeSet := by
  obtain ⟨M, hM, hsub, hmax⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_supergraph L hL
  refine ⟨M, hM, hsub, ?_⟩
  intro hback
  have hEq : M.edgeSet = L.edgeSet := Set.Subset.antisymm hback hsub
  have hcount :=
    WilliamsonShmoys.planar_edge_maximal_euler_count M hM hmax hV
  rw [hEq] at hcount
  omega
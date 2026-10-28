-- Prove2me | solution 1 for WilliamsonShmoys.planar_strict_supergraph_below_triangulation_bound_3909e30c_a531_4010_a48d_ad4d6b0818e8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T14:49:30.930095+00:00
-- url     : https://prove2.me/submissions/4d34130a-d4c7-479e-be99-7eb4e12e2c87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hsmall : J.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K ≠ J := by
  obtain ⟨K, hJK, hK, hKcard⟩ :=
    WilliamsonShmoys.planar_completion_edge_bound J hV hJ
  refine ⟨K, hJK, hK, ?_⟩
  intro hEq
  rw [← hEq] at hsmall
  rw [hKcard] at hsmall
  omega
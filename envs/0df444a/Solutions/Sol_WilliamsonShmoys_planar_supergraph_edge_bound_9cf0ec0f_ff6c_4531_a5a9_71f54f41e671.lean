-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:58:05.017669+00:00
-- url     : https://prove2.me/submissions/6a634b25-3c1f-410f-9583-5a7a183b8315

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_maximal_supergraph_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * (Fintype.card V : Int) - 6 ≤ (L.edgeSet.ncard : Int) := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.drawable_maximal_supergraph_extension K hK hCard
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_equations L hL hMax hCard
  refine ⟨L, hKL, hL, ?_⟩
  have hNat : 3 * Fintype.card V = L.edgeSet.ncard + 6 := by omega
  have hInt : 3 * (Fintype.card V : Int) = (L.edgeSet.ncard : Int) + 6 := by
    exact_mod_cast hNat
  omega
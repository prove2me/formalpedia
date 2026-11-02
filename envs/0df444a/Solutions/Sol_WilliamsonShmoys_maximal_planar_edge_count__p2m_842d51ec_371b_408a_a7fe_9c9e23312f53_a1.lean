-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_842d51ec_371b_408a_a7fe_9c9e23312f53_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:33:02.006255+00:00
-- url     : https://prove2.me/submissions/a9343f64-d490-47e9-8d8c-4b4bac0b1b5d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_61f827a4_90a1_438d_8856_22a36ff94a2a_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hplanar : HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ->
      HasPlanarDrawingOn L ->
      L.edgeSet = K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hsub, hdraw, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_61f827a4_90a1_438d_8856_22a36ff94a2a_a2
      K hcard hplanar
  have hEq : L.edgeSet = K.edgeSet := hmax L hsub hdraw
  rw [hEq] at hcount
  exact hcount
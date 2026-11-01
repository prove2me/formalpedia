-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_49e59269_0942_49a7_bb42_8d7dcf799486_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:01:56.975195+00:00
-- url     : https://prove2.me/submissions/8a5f48cb-8c9d-46fb-a85e-57f069ad6a2f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_simpleGraph_predicate_maximal_extension__p2m_f94053f9_aa1c_4659_90f3_4794e32e1f9a_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {U : Type} [Fintype U] [LinearOrder U]
    (H : SimpleGraph U)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph U, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph U, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → K = L := by
  exact finite_simpleGraph_predicate_maximal_extension__p2m_f94053f9_aa1c_4659_90f3_4794e32e1f9a_a1
    H WilliamsonShmoys.HasPlanarDrawingOn hdraw
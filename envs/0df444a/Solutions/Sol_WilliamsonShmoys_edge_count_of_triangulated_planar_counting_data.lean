-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_triangulated_planar_counting_data
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:13:57.081772+00:00
-- url     : https://prove2.me/submissions/6a17f0c3-8208-40c5-a35c-4602cbce2574

import Definitions.Def_WilliamsonShmoys_TriangulatedPlanarCountingData
import Mathlib.Tactic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (D : WilliamsonShmoys.TriangulatedPlanarCountingData K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hEuler := D.euler
  have hFace := D.face_degree_sum
  have hInt : (K.edgeSet.ncard : Int) + 6 = 3 * (Fintype.card V : Int) := by
    omega
  exact_mod_cast hInt

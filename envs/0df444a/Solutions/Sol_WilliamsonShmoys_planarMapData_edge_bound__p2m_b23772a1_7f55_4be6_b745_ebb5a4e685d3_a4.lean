-- Prove2me | solution 1 for WilliamsonShmoys.planarMapData_edge_bound__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:04:25.579201+00:00
-- url     : https://prove2.me/submissions/fba21da4-70a6-4270-985e-12941a326c6e

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (D : PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3 J) :
    J.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  have hface_lower :
      D.faceCount * 3 <= 2 * J.edgeFinset.card := by
    calc
      D.faceCount * 3 =
          Finset.sum Finset.univ (fun _ : Fin D.faceCount => (3 : Nat)) := by simp
      _ <= Finset.sum Finset.univ (fun f : Fin D.faceCount => D.faceDegree f) :=
        Finset.sum_le_sum fun f _ => D.faceDegree_ge_three f
      _ = 2 * J.edgeFinset.card := D.sum_faceDegree
  nlinarith [hface_lower, D.euler]

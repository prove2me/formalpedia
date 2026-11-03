-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_boundary_bound__p2m_dbfda827_a827_4911_8354_de916f36b6c0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:11:48.09628+00:00
-- url     : https://prove2.me/submissions/72d39a35-81d3-4c60-89ee-9b2f64b42b91

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_e44127b7_e307_4dd9_bc34_b67b377ea4eb_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    ∀ f : ℕ, Fintype.card V + f = K.edgeFinset.card + 2 →
      3 * f <= 2 * K.edgeFinset.card := by
  intro f heuler
  have hedge := WilliamsonShmoys.simple_planar_edge_bound__p2m_e44127b7_e307_4dd9_bc34_b67b377ea4eb_a1
    K dK hconn hK hcard
  omega
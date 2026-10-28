-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound_job_d022b1d1_d1e3_4932_940e_a619c500f998
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:15:55.645122+00:00
-- url     : https://prove2.me/submissions/6fcdcd7c-caf1-4410-af33-e40b418591a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationCertificate
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_certificate_of_drawing
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_certificate_edge_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) : G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  cases WilliamsonShmoys.planar_triangulation_certificate_of_drawing G hdraw hconn hV with
  | intro c => exact WilliamsonShmoys.planar_triangulation_certificate_edge_bound G c
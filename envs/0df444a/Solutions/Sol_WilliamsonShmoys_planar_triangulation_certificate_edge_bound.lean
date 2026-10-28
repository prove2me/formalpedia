-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_certificate_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:36:14.131401+00:00
-- url     : https://prove2.me/submissions/1fed9357-453b-4c2a-8660-79116f530848

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationCertificate

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (c : PlanarTriangulationCertificate G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  have hle : G ≤ c.extension := by
    intro u v huv
    exact c.contains u v huv
  have hsub : G.edgeSet ⊆ c.extension.edgeSet :=
    (SimpleGraph.edgeSet_subset_edgeSet).2 hle
  have hcount : G.edgeSet.ncard ≤ c.extension.edgeSet.ncard :=
    Set.ncard_mono hsub
  have heuler := c.euler
  have htriangular := c.triangular
  have hext : c.extension.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    omega
  omega
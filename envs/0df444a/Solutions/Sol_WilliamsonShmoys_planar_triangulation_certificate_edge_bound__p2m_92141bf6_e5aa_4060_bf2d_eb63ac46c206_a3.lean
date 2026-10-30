-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_certificate_edge_bound__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:49:58.514711+00:00
-- url     : https://prove2.me/submissions/2bbb2db1-2093-4731-acf8-d1408d9091cc

import Mathlib
import Definitions.Def_PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (c : WilliamsonShmoys.PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3 H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  have hsum : 3 * c.faces.card ≤ ∑ f ∈ c.faces, c.faceDegree f := by
    calc
      3 * c.faces.card = ∑ _f ∈ c.faces, 3 := by simp [mul_comm]
      _ ≤ ∑ f ∈ c.faces, c.faceDegree f := by
        apply Finset.sum_le_sum
        intro f hf
        exact c.faceDegree_ge_three f hf
  have hsuper : c.supergraph.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
    have hcount : 3 * c.faces.card ≤ 2 * c.supergraph.edgeSet.ncard := by
      rw [← c.incidence]
      exact hsum
    have heuler := c.euler
    omega
  have hsub : H.edgeSet ⊆ c.supergraph.edgeSet := by
    apply SimpleGraph.edgeSet_mono
    intro u v huv
    exact c.contains huv
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans hsuper
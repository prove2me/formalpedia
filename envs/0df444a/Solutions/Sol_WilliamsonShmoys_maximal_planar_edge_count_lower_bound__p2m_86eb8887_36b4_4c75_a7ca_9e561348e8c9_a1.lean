-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_86eb8887_36b4_4c75_a7ca_9e561348e8c9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:54:19.158462+00:00
-- url     : https://prove2.me/submissions/3775d435-3327-4214-9d53-57059b34ead9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_924b9ea4_0b38_4572_b493_5a5eee48f103_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    (∀ L : SimpleGraph V,
      K.edgeFinset ⊆ L.edgeFinset →
      HasPlanarDrawingOn L →
      L.edgeFinset = K.edgeFinset) →
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by
  classical
  intro hmax
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation__p2m_924b9ea4_0b38_4572_b493_5a5eee48f103_a2
      K hcard hK
  have hEq : L.edgeFinset = K.edgeFinset := hmax L hKL hL
  rw [hEq] at hcount
  omega
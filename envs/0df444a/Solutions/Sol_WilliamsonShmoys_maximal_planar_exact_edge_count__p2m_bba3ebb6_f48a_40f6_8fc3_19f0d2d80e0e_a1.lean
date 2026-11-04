-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_bba3ebb6_f48a_40f6_8fc3_19f0d2d80e0e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:41:23.760048+00:00
-- url     : https://prove2.me/submissions/95725b4d-24d4-4091-8f46-c8cfd657a369

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_86eb8887_36b4_4c75_a7ca_9e561348e8c9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_86eb8887_36b4_4c75_a7ca_9e561348e8c9_a1

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
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : ∀ L : SimpleGraph V, DecidableRel L.Adj :=
    fun L => Classical.decRel L.Adj
  intro hmax
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_86eb8887_36b4_4c75_a7ca_9e561348e8c9_a1
    K hcard hK
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_86eb8887_36b4_4c75_a7ca_9e561348e8c9_a1
    K hcard hK hmax
  omega
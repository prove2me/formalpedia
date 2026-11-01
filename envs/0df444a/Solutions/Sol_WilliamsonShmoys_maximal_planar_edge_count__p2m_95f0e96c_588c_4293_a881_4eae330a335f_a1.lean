-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_95f0e96c_588c_4293_a881_4eae330a335f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:40:49.914128+00:00
-- url     : https://prove2.me/submissions/c4767f01-f7f5-4f86-9ff9-4881e1e18ec8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_8532617a_0690_495a_a2cc_fdaf4080cf05_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_bound__p2m_8532617a_0690_495a_a2cc_fdaf4080cf05_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V,
      T.edgeSet ⊆ U.edgeSet →
      (∃ e, e ∈ U.edgeSet ∧ e ∉ T.edgeSet) →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hup : T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_8532617a_0690_495a_a2cc_fdaf4080cf05_a1
      T hT hcard
  have hlo : 3 * Fintype.card V - 6 ≤ T.edgeSet.ncard := by
    by_contra hnot
    have hlt : T.edgeSet.ncard < 3 * Fintype.card V - 6 := Nat.lt_of_not_ge hnot
    obtain ⟨U, hsub, e, heU, heT, hU⟩ :=
      WilliamsonShmoys.planar_edge_augmentation_below_bound__p2m_8532617a_0690_495a_a2cc_fdaf4080cf05_a1
        T hT hcard hlt
    exact hmax U hsub ⟨e, heU, heT⟩ hU
  omega
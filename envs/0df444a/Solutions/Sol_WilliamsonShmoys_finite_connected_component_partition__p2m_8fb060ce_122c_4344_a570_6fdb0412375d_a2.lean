-- Prove2me | solution 1 for WilliamsonShmoys.finite_connected_component_partition__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:47:19.279205+00:00
-- url     : https://prove2.me/submissions/7fcb04f1-d2e1-405d-a226-3a7e5a8e0512
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_component_partition_core__p2m_43810500_1f43_4f26_9fb2_357a895d104d_a1
import Theorems.Thm_WilliamsonShmoys_component_edge_sum__p2m_43810500_1f43_4f26_9fb2_357a895d104d_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     ∃ C : Finset (Finset V),
      (∀ B ∈ C, 0 < B.card) ∧
      (∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ →
        Disjoint (↑B₁ : Set V) (↑B₂ : Set V)) ∧
      (∀ v : V, ∃ B ∈ C, v ∈ B) ∧
      Fintype.card V = ∑ B ∈ C, B.card ∧
      (∀ B ∈ C,
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).Connected) ∧
      (∀ B ∈ C, B.card = 1 →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).edgeFinset.card = 0) ∧
      (∀ B ∈ C, B.card = 2 →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).edgeFinset.card ≤ 1) ∧
      N.edgeFinset.card =
        ∑ B ∈ C,
          (letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _;
           (N.induce (↑B : Set V)).edgeFinset.card)) := by
  classical
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  obtain ⟨C, hnonempty, hdisjoint, hcover, hvertices, hconnected,
      hsingle, hpair⟩ :=
    WilliamsonShmoys.finite_component_partition_core__p2m_43810500_1f43_4f26_9fb2_357a895d104d_a1 N
  refine ⟨C, hnonempty, hdisjoint, hcover, hvertices, hconnected, hsingle, hpair, ?_⟩
  exact WilliamsonShmoys.component_edge_sum__p2m_43810500_1f43_4f26_9fb2_357a895d104d_a1
    N C hdisjoint hcover
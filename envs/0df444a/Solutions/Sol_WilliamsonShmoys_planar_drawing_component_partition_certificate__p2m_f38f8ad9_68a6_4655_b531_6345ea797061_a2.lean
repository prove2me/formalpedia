-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_component_partition_certificate__p2m_f38f8ad9_68a6_4655_b531_6345ea797061_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:29:55.696124+00:00
-- url     : https://prove2.me/submissions/59fabc1d-bbca-43c1-b07a-8d84cc1915b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_connected_component_partition__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_induce__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     ∃ C : Finset (Finset V),
      (∀ B ∈ C, 0 < B.card) ∧
      (∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ →
        Disjoint (↑B₁ : Set V) (↑B₂ : Set V)) ∧
      (∀ v : V, ∃ B ∈ C, v ∈ B) ∧
      Fintype.card V = ∑ B ∈ C, B.card ∧
      (∀ B ∈ C, 3 ≤ B.card →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).Connected ∧
        HasPlanarDrawingOn (N.induce (↑B : Set V))) ∧
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
  obtain ⟨C, hpos, hdisj, hcover, hverts, hlarge, hsingle, hpair, hedges⟩ :=
    WilliamsonShmoys.finite_connected_component_partition__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2 N
  refine ⟨C, hpos, hdisj, hcover, hverts, ?_, hsingle, hpair, hedges⟩
  intro B hB hlargeB
  letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
  constructor
  · exact hlarge B hB
  · exact WilliamsonShmoys.planar_drawing_induce__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2
      N hN (↑B : Set V)
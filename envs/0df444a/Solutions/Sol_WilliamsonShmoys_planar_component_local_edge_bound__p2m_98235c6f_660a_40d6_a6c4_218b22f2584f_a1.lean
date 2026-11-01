-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_local_edge_bound__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:49:11.795198+00:00
-- url     : https://prove2.me/submissions/0aee589a-231b-468b-8ee4-e25edafa62e5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (parts : Finset (Finset V))
    (hnonempty : ∀ C, C ∈ parts → C.Nonempty)
    (hconn : ∀ C, C ∈ parts → (M.induce (C : Set V)).Connected)
    (hdraw : ∀ C, C ∈ parts → WilliamsonShmoys.HasPlanarDrawingOn (M.induce (C : Set V)))
    (hlarge : ∀ C, C ∈ parts →
      3 ≤ Fintype.card {x : V // x ∈ C} →
      (M.induce (C : Set V)).edgeSet.ncard + 6 ≤
        3 * Fintype.card {x : V // x ∈ C}) :
    ∀ C, C ∈ parts →
      (M.induce (C : Set V)).edgeSet.ncard +
        (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6
         else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3)
        ≤ 3 * Fintype.card {x : V // x ∈ C} := by
  classical
  intro C hC
  let G := M.induce (C : Set V)
  let n := Fintype.card {x : V // x ∈ C}
  have hcard : n = C.card := by simp [n]
  by_cases hn : 3 ≤ C.card
  · have hn' : 3 ≤ n := by simpa [hcard] using hn
    simpa [G, n, hcard, hn] using hlarge C hC hn'
  · have hpos : 0 < n := by
      rw [hcard]
      exact Finset.card_pos.mpr (hnonempty C hC)
    have hnsmall : n = 1 ∨ n = 2 := by omega
    have hedge : G.edgeSet.ncard ≤ n.choose 2 := by
      calc
        G.edgeSet.ncard = Fintype.card G.edgeSet := (Set.fintypeCard_eq_ncard _).symm
        _ = G.edgeFinset.card := G.card_edgeSet
        _ ≤ n.choose 2 := by
          simpa [n] using G.card_edgeFinset_le_card_choose_two
    have hnCsmall : C.card = 1 ∨ C.card = 2 := by omega
    have hedgeC : G.edgeSet.ncard ≤ C.card.choose 2 := by
      simpa [n, hcard] using hedge
    rcases hnCsmall with hC1 | hC2
    · have hedge0 : G.edgeSet.ncard ≤ 0 := by simpa [hC1] using hedgeC
      have hgoal : G.edgeSet.ncard + 3 ≤ 3 * Fintype.card {x : V // x ∈ C} := by
        simpa [G, n, hcard, hC1] using (show G.edgeSet.ncard + 3 ≤ 3 * C.card by omega)
      simpa [G, n, hcard, hC1, hn] using hgoal
    · have hedge1 : G.edgeSet.ncard ≤ 1 := by simpa [hC2] using hedgeC
      have hgoal : G.edgeSet.ncard + 5 ≤ 3 * Fintype.card {x : V // x ∈ C} := by
        simpa [G, n, hcard, hC2] using (show G.edgeSet.ncard + 5 ≤ 3 * C.card by omega)
      simpa [G, n, hcard, hC2, hn] using hgoal
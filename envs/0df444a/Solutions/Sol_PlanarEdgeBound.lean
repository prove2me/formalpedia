-- Prove2me | solution 1 for PlanarEdgeBound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T21:21:38.528074+00:00
-- url     : https://prove2.me/submissions/ccd058e1-3210-4ff4-aa79-b2ec3147d68a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ConnectedPlanarEdgeBound
import Theorems.Thm_InducedSubdrawingBridge
import Definitions.Def_OrdinaryPolygonalDrawing
import Theorems.Thm_SimpleGraphComponentEdgeSumBound

open Classical
noncomputable section

-- [TABLET NODE: PlanarEdgeBound]
theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    (∃ D : OrdinaryPolygonalDrawing G, D.crossingSet.card = 0) →
      G.edgeFinset.card ≤ 3 * Fintype.card V := by
  classical
  intro hdraw
  letI : DecidableEq V := Classical.decEq V
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases hdraw with ⟨D, hD⟩
  exact SimpleGraphComponentEdgeSumBound G (fun c => by
    by_cases hlarge : 3 ≤ Fintype.card c.supp
    · rcases InducedSubdrawingBridge G D c.supp with
        ⟨DX, _hvertex, _hedges, hcross, _hadjacent⟩
      have hDXzero : DX.crossingSet.card = 0 := by
        apply Finset.card_eq_zero.mpr
        ext p
        constructor
        · intro hp
          rcases (hcross p).1 hp with ⟨e₁, e₂, h₁₂, _hS₁, _hS₂, hp₁, hp₂⟩
          have hpD : p ∈ D.crossingSet :=
            (D.crossingSet_spec p).2 ⟨e₁, e₂, h₁₂, hp₁, hp₂⟩
          have hDempty : D.crossingSet = ∅ := Finset.card_eq_zero.mp hD
          rw [hDempty] at hpD
          exact hpD
        · intro hp
          simp at hp
      have hconn : (G.induce c.supp).Connected := by
        simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using
          (SimpleGraph.ConnectedComponent.connected_toSimpleGraph c)
      have hbound :
          (G.induce c.supp).edgeFinset.card ≤
            3 * Fintype.card c.supp - 6 :=
        ConnectedPlanarEdgeBound (G.induce c.supp) hconn hlarge ⟨DX, hDXzero⟩
      omega
    · have hnle : Fintype.card c.supp ≤ 2 := by omega
      have hchoose :
          (G.induce c.supp).edgeFinset.card ≤ (Fintype.card c.supp).choose 2 := by
        exact SimpleGraph.card_edgeFinset_le_card_choose_two (G := G.induce c.supp)
      have hcases :
          Fintype.card c.supp = 0 ∨ Fintype.card c.supp = 1 ∨
            Fintype.card c.supp = 2 := by
        omega
      rcases hcases with h0 | h1 | h2
      · calc
          (G.induce c.supp).edgeFinset.card
              ≤ (Fintype.card c.supp).choose 2 := hchoose
          _ ≤ 3 * Fintype.card c.supp := by rw [h0]; simp
      · calc
          (G.induce c.supp).edgeFinset.card
              ≤ (Fintype.card c.supp).choose 2 := hchoose
          _ ≤ 3 * Fintype.card c.supp := by rw [h1]; simp
      · calc
          (G.induce c.supp).edgeFinset.card
              ≤ (Fintype.card c.supp).choose 2 := hchoose
          _ ≤ 3 * Fintype.card c.supp := by rw [h2]; simp)

-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_insert_graph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:59:21.862548+00:00
-- url     : https://prove2.me/submissions/370c08be-3c3e-41af-90dd-c1a341b3b904

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (hdisconnected : ¬ Relation.ReflTransGen H.Adj u v) :
    let K : SimpleGraph V :=
      SimpleGraph.fromEdgeSet (insert s(u, v) H.edgeSet)
    (∀ {x y : V}, H.Adj x y → K.Adj x y) ∧
      (∃ e : Sym2 V, e ∉ H.edgeSet ∧ K.edgeSet = insert e H.edgeSet) ∧
      K.Adj u v := by
  have huv : u ≠ v := by
    intro h
    subst v
    exact hdisconnected Relation.ReflTransGen.refl
  have hnot : ¬ H.Adj u v := by
    intro h
    exact hdisconnected (Relation.ReflTransGen.single h)
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    have hxyne : x ≠ y := hxy.ne
    simp [SimpleGraph.fromEdgeSet_adj, hxy, hxyne]
  · refine ⟨s(u, v), ?_, ?_⟩
    · intro he
      exact hnot (by simpa using he)
    · ext e
      simp only [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_insert_iff]
      constructor
      · rintro ⟨he | he, hdiag⟩
        · exact Or.inl he
        · exact Or.inr he
      · intro he
        constructor
        · exact he
        · intro hdiag
          rcases he with he | he
          · subst e
            exact (by simpa [Sym2.mk_isDiag_iff, huv] using hdiag)
          · exact (H.not_isDiag_of_mem_edgeSet he) hdiag
  · simp [SimpleGraph.fromEdgeSet_adj, huv]
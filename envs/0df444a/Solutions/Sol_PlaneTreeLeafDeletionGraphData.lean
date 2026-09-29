-- Prove2me | solution 1 for PlaneTreeLeafDeletionGraphData
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T19:05:28.210889+00:00
-- url     : https://prove2.me/submissions/eb1568bf-bb90-4c7a-9206-a60037b129ea

import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

-- [TABLET NODE: PlaneTreeLeafDeletionGraphData]
theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj]
    (hTree : G.IsTree) (hEdges : G.edgeSet ≠ ∅) :
    ∃ v w : V, G.degree v = 1 ∧ v ≠ w ∧ G.Adj v w ∧
      (∀ u : V, G.Adj v u → u = w) ∧
        (G.induce ({v}ᶜ : Set V)).IsTree ∧
          ∃ e : G.edgeFinset, e.1 = Sym2.mk v w := by
  have hNontrivial : Nontrivial V := by
    have hEdgeNonempty : G.edgeSet.Nonempty := Set.nonempty_iff_ne_empty.mpr hEdges
    rcases hEdgeNonempty with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf a b =>
        have hab : G.Adj a b := by
          simpa using he
        exact ⟨⟨a, b, hab.ne⟩⟩
  obtain ⟨v, hvdeg⟩ := hTree.exists_vert_degree_one_of_nontrivial
  obtain ⟨w, hvw, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hvdeg
  have hIndTree : (G.induce ({v}ᶜ : Set V)).IsTree := by
    constructor
    · exact hTree.connected.induce_compl_singleton_of_degree_eq_one hvdeg
    · exact hTree.isAcyclic.induce ({v}ᶜ : Set V)
  refine ⟨v, w, hvdeg, hvw.ne, hvw, ?_, hIndTree, ?_⟩
  · intro u hu
    exact huniq u hu
  · refine ⟨⟨Sym2.mk v w, ?_⟩, rfl⟩
    exact (SimpleGraph.mem_edgeFinset).mpr (by simpa using hvw)

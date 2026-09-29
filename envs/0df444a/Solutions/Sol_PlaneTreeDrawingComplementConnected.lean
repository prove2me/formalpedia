-- Prove2me | solution 1 for PlaneTreeDrawingComplementConnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T18:55:59.685998+00:00
-- url     : https://prove2.me/submissions/6dd67bc0-42c4-49f6-ac6d-1eebc058ffa0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PlaneTreeNoEdgeComplementConnected
import Theorems.Thm_PlaneTreeLeafDeletionGraphData
import Theorems.Thm_PlaneTreeLeafDeletionDrawingData
import Theorems.Thm_PlaneTreeLeafPendantAttachment
import Theorems.Thm_PendantArcComplementConnected
import Theorems.Thm_OrdinaryDrawingImageCompact
import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonallyPathConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

universe u

-- [TABLET NODE: PlaneTreeDrawingComplementConnected]
theorem solution {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0) :
    G.IsTree → PolygonallyPathConnected ((OrdinaryDrawingImage G D)ᶜ) := by
  intro hTree
  have hTreeComplementConnected :
      ∀ n : ℕ,
        ∀ {W : Type u} [Fintype W] (H : SimpleGraph W) [Fintype H.edgeSet]
          [DecidableRel H.Adj] (E : OrdinaryPolygonalDrawing H),
          H.edgeFinset.card = n →
            E.crossingSet.card = 0 →
              H.IsTree →
                PolygonallyPathConnected ((OrdinaryDrawingImage H E)ᶜ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro W _ H _ _ E hcard hE hTree
        by_cases hNoEdges : H.edgeSet = ∅
        · exact PlaneTreeNoEdgeComplementConnected H E hTree hNoEdges
        · obtain ⟨v, w, hvDegree, hvw_ne, hvw, hLeaf, hDeletedTree, e, he⟩ :=
            PlaneTreeLeafDeletionGraphData H hTree hNoEdges
          have hDeletedInducedTree : (H.induce ({v}ᶜ : Set W)).IsTree := hDeletedTree
          have hDeletedLeafEdge : e.1 = Sym2.mk v w := he
          obtain
            ⟨D', hD'_crossing, hD'_vertex, hD'_edges, hImage, hAttach_mem,
              hLeafEndpoint_notMem, hEdgeDecrease, hEndpointOrientation⟩ :=
            PlaneTreeLeafDeletionDrawingData H E hE hTree hvDegree hvw_ne hvw hLeaf
              hDeletedInducedTree e hDeletedLeafEdge
          have hSmaller : (H.induce ({v}ᶜ : Set W)).edgeFinset.card < n := by
            simpa [hcard] using hEdgeDecrease
          have hInduction :
              PolygonallyPathConnected
                ((OrdinaryDrawingImage (H.induce ({v}ᶜ : Set W)) D')ᶜ) := by
            exact ih (H.induce ({v}ᶜ : Set W)).edgeFinset.card hSmaller
              (H.induce ({v}ᶜ : Set W)) D' rfl hD'_crossing hDeletedInducedTree
          have hPendant :
              (((E.edgeArc e).carrier ∩
                  OrdinaryDrawingImage (H.induce ({v}ᶜ : Set W)) D' =
                    ({(E.edgeArc e).source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                  (E.edgeArc e).target ∉
                    OrdinaryDrawingImage (H.induce ({v}ᶜ : Set W)) D') ∨
                ((E.edgeArc e).carrier ∩
                  OrdinaryDrawingImage (H.induce ({v}ᶜ : Set W)) D' =
                    ({(E.edgeArc e).target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                  (E.edgeArc e).source ∉
                    OrdinaryDrawingImage (H.induce ({v}ᶜ : Set W)) D')) := by
            exact PlaneTreeLeafPendantAttachment H E hE e D' hD'_vertex hD'_edges
              hAttach_mem hLeafEndpoint_notMem hEndpointOrientation
          have hAdded :
              PolygonallyPathConnected
                ((OrdinaryDrawingImage (H.induce ({v}ᶜ : Set W)) D' ∪
                    (E.edgeArc e).carrier)ᶜ) :=
            PendantArcComplementConnected
              (OrdinaryDrawingImage (H.induce ({v}ᶜ : Set W)) D') (E.edgeArc e)
              (OrdinaryDrawingImageCompact (H.induce ({v}ᶜ : Set W)) D')
              hInduction hPendant
          simpa [hImage] using hAdded
  exact hTreeComplementConnected G.edgeFinset.card G D rfl hD hTree

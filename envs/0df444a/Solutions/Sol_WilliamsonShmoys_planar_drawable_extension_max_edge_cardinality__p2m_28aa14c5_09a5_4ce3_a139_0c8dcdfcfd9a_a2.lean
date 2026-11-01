-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_extension_max_edge_cardinality__p2m_28aa14c5_09a5_4ce3_a139_0c8dcdfcfd9a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:02:59.766183+00:00
-- url     : https://prove2.me/submissions/251f73d7-2d2f-4887-93ba-83506d23cd99

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (dW : DecidableRel W.Adj)
    (hW : HasPlanarDrawingOn W) :
    ∃ (T : SimpleGraph V) (dT : DecidableRel T.Adj),
      HasPlanarDrawingOn T ∧
      (letI : DecidableRel W.Adj := dW
       letI : DecidableRel T.Adj := dT
       W.edgeFinset ⊆ T.edgeFinset) ∧
      (∀ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
        HasPlanarDrawingOn U →
        (letI : DecidableRel W.Adj := dW
         letI : DecidableRel U.Adj := dU
         W.edgeFinset ⊆ U.edgeFinset) →
        (letI : DecidableRel T.Adj := dT
         letI : DecidableRel U.Adj := dU
         U.edgeFinset.card ≤ T.edgeFinset.card)) := by
  classical
  letI : DecidableRel W.Adj := dW
  let P : SimpleGraph V → Prop := fun G => HasPlanarDrawingOn G ∧ W ≤ G
  have hPW : P W := ⟨hW, le_rfl⟩
  have hfinite : {G : SimpleGraph V | P G}.Finite := Set.toFinite _
  obtain ⟨T, hPT, hmax⟩ :=
    Set.exists_max_image {G : SimpleGraph V | P G} (fun G => Nat.card G.edgeSet)
      hfinite ⟨W, hPW⟩
  refine ⟨T, inferInstance, hPT.1, ?_, ?_⟩
  · simpa only [SimpleGraph.edgeFinset_subset_edgeFinset] using hPT.2
  · intro U dU hU hWU
    letI : DecidableRel U.Adj := dU
    have hWU' : W ≤ U := by
      simpa only [SimpleGraph.edgeFinset_subset_edgeFinset] using hWU
    have hmax' : Nat.card U.edgeSet ≤ Nat.card T.edgeSet := hmax U ⟨hU, hWU'⟩
    have hUcard : U.edgeFinset.card = Nat.card U.edgeSet := by
      rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
    have hTcard : T.edgeFinset.card = Nat.card T.edgeSet := by
      rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
    omega
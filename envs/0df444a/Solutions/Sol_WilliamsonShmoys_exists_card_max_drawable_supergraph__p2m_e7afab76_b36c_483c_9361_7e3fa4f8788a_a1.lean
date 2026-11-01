-- Prove2me | solution 1 for WilliamsonShmoys.exists_card_max_drawable_supergraph__p2m_e7afab76_b36c_483c_9361_7e3fa4f8788a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:49:30.267541+00:00
-- url     : https://prove2.me/submissions/e8c1efd6-4165-40fb-94ba-49fa41475e9f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open Finset

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ (L : SimpleGraph V) [DecidableRel L.Adj],
        H.edgeFinset ⊆ L.edgeFinset →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeFinset.card ≤ K.edgeFinset.card) := by
  classical
  let p : SimpleGraph V → Prop := fun G => H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hp : ∃ G : SimpleGraph V, p G := by
    exact ⟨H, le_rfl, hH⟩
  obtain ⟨K, instK, hK⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (p := p)).2 hp
  letI : DecidableRel K.Adj := instK
  refine ⟨K, instK, ?_, hK.1.2, ?_⟩
  · simpa only [SimpleGraph.edgeFinset_subset_edgeFinset] using hK.1.1
  · intro L instL hHL hL
    letI : DecidableRel L.Adj := instL
    have hLE : H ≤ L := (SimpleGraph.edgeFinset_subset_edgeFinset).1 hHL
    exact hK.2 ⟨hLE, hL⟩
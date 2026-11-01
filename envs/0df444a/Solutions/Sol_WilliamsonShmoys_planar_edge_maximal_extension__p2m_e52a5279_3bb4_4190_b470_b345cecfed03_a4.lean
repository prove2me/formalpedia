-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_extension__p2m_e52a5279_3bb4_4190_b470_b345cecfed03_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:11:38.617193+00:00
-- url     : https://prove2.me/submissions/cad9b701-55c1-4da9-b1b6-4f6393920390

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    Exists fun H : SimpleGraph V =>
      (forall {u v : V}, G.Adj u v -> H.Adj u v) /\
      (HasPlanarDrawingOn H /\
        forall K : SimpleGraph V, HasPlanarDrawingOn K ->
          (forall {u v : V}, H.Adj u v -> K.Adj u v) ->
          (forall {u v : V}, K.Adj u v -> H.Adj u v)) := by
  classical
  let p : SimpleGraph V -> Prop := fun K => HasPlanarDrawingOn K /\ G <= K
  obtain ⟨H, _instH, hH⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 ⟨G, hG, le_rfl⟩
  refine ⟨H, ?_, hH.1.1, ?_⟩
  · intro u v huv
    exact hH.1.2 huv
  · intro K hK hHK u v huv
    have hHKle : H <= K := by
      intro a b hab
      exact hHK hab
    have hGK : G <= K := hH.1.2.trans hHKle
    have hmax : K.edgeFinset.card <= H.edgeFinset.card := by
      exact hH.2 ⟨hK, hGK⟩
    have hsub : H.edgeFinset ⊆ K.edgeFinset :=
      SimpleGraph.edgeFinset_subset_edgeFinset.mpr hHKle
    have heq : H.edgeFinset = K.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsub hmax
    have hgraph : H = K := SimpleGraph.edgeFinset_inj.mp heq
    simpa [hgraph] using huv
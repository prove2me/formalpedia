-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_max_card__p2m_0b3013ac_25d6_4dd0_b6f8_fc82fd3d8fbf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:23:01.186655+00:00
-- url     : https://prove2.me/submissions/ced42ea4-ed5b-4129-a7c0-357660163635

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      G.edgeFinset ⊆ K.edgeFinset ∧
      (∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn L →
        G.edgeFinset ⊆ L.edgeFinset →
        L.edgeFinset.card ≤ K.edgeFinset.card) := by
  classical
  let p : SimpleGraph V → Prop := fun H =>
    WilliamsonShmoys.HasPlanarDrawingOn H ∧ G ≤ H
  have hp : ∃ H : SimpleGraph V, p H := by
    exact ⟨G, hG, le_rfl⟩
  obtain ⟨K, dK, hK⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (V := V) p).2 hp
  letI : DecidableRel G.Adj := dG
  letI : DecidableRel K.Adj := dK
  refine ⟨K, dK, hK.1.1, ?_, ?_⟩
  · exact SimpleGraph.edgeFinset_subset_edgeFinset.2 hK.1.2
  · intro L dL hL hsub
    letI : DecidableRel L.Adj := dL
    have hGL : G ≤ L := SimpleGraph.edgeFinset_subset_edgeFinset.1 hsub
    exact hK.2 ⟨hL, hGL⟩
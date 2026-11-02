-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_maxEdge__p2m_0e267cb6_c5af_47f0_9958_0b72bfd3b3ee_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:53:21.124274+00:00
-- url     : https://prove2.me/submissions/1c2c10ca-e618-4470-bea9-6e94136a27e6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, ∃ (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH
       G.edgeFinset ⊆ H.edgeFinset ∧
       WilliamsonShmoys.HasPlanarDrawingOn H ∧
       ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
         letI : DecidableRel K.Adj := dK
         WilliamsonShmoys.HasPlanarDrawingOn K →
         H.edgeFinset ⊆ K.edgeFinset →
         K.edgeFinset.card ≤ H.edgeFinset.card) := by
  classical
  let feasible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun H =>
      G.edgeFinset ⊆ H.edgeFinset ∧ WilliamsonShmoys.HasPlanarDrawingOn H
  have hGmem : G ∈ feasible := by
    simp [feasible, hG]
  obtain ⟨H, hHm, hmax⟩ :=
    feasible.exists_max_image (fun H => H.edgeFinset.card) ⟨G, hGmem⟩
  refine ⟨H, Classical.decRel H.Adj, ?_⟩
  change G.edgeFinset ⊆ H.edgeFinset ∧
    WilliamsonShmoys.HasPlanarDrawingOn H ∧ _
  have hHfeas := (Finset.mem_filter.mp hHm).2
  refine ⟨hHfeas.1, hHfeas.2, ?_⟩
  intro K dK hKplanar hHK
  have hdK : dK = Classical.decRel K.Adj := Subsingleton.elim _ _
  subst dK
  have hKmem : K ∈ feasible := by
    simp only [feasible, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.Subset.trans hHfeas.1 hHK, hKplanar⟩
  exact hmax K hKmem
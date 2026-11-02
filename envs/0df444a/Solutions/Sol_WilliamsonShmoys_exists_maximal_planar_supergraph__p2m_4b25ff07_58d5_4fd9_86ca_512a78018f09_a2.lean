-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4b25ff07_58d5_4fd9_86ca_512a78018f09_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:16:26.579765+00:00
-- url     : https://prove2.me/submissions/dc00e84f-5fa8-4dc1-bda7-977156f90aec

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    ∃ L : SimpleGraph V,
      K.edgeFinset ⊆ L.edgeFinset ∧
      HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeFinset ⊆ M.edgeFinset →
        HasPlanarDrawingOn M →
        M.edgeFinset = L.edgeFinset := by
  classical
  let p : SimpleGraph V → Prop :=
    fun G => K.edgeFinset ⊆ G.edgeFinset ∧ HasPlanarDrawingOn G
  have hp : ∃ G : SimpleGraph V, p G := by
    refine ⟨K, ?_⟩
    exact ⟨by intro e he; exact he, hK⟩
  obtain ⟨L, dL, hL⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (V := V) p).2 hp
  have hdL : dL = Classical.decRel L.Adj := Subsingleton.elim _ _
  subst dL
  refine ⟨L, hL.1.1, hL.1.2, ?_⟩
  intro M hLM hM
  have hMp : p M := ⟨Finset.Subset.trans hL.1.1 hLM, hM⟩
  have hle : L ≤ M := SimpleGraph.edgeFinset_subset_edgeFinset.1 hLM
  have heq : L = M :=
    (SimpleGraph.IsExtremal.le_iff_eq hL hMp).1 hle
  simpa [heq]
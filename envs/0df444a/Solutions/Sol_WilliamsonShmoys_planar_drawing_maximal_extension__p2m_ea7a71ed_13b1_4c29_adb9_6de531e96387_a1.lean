-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ea7a71ed_13b1_4c29_adb9_6de531e96387_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:02:53.068443+00:00
-- url     : https://prove2.me/submissions/6c6cb4cb-80bc-4205-b657-bdb3021b18bd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      K.edgeFinset ⊆ L.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn M →
        L.edgeFinset ⊆ M.edgeFinset → M.edgeFinset ⊆ L.edgeFinset := by
  classical
  let P : SimpleGraph V → Prop := fun G => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  obtain ⟨L, dL, hL⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (V := V) P).2
      ⟨K, ⟨le_rfl, hK⟩⟩
  have hKL : K ≤ L := hL.1.1
  refine ⟨L, dL, SimpleGraph.edgeFinset_subset_edgeFinset.2 hKL, hL.1.2, ?_⟩
  intro M dM hM hLM
  have hLM' : L ≤ M := SimpleGraph.edgeFinset_subset_edgeFinset.1 hLM
  have hPM : P M := ⟨hKL.trans hLM', hM⟩
  have hcard : M.edgeFinset.card ≤ L.edgeFinset.card := hL.2 (G' := M) hPM
  have heq : L.edgeFinset = M.edgeFinset :=
    Finset.eq_of_subset_of_card_le hLM hcard
  exact heq.symm.subset

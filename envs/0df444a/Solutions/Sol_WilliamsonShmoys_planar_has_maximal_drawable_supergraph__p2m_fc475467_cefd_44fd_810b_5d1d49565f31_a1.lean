-- Prove2me | solution 1 for WilliamsonShmoys.planar_has_maximal_drawable_supergraph__p2m_fc475467_cefd_44fd_810b_5d1d49565f31_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:58:41.239777+00:00
-- url     : https://prove2.me/submissions/78e8a069-02d7-4284-89af-12a28eaa9716

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨K, ?_⟩
    simp [S, hK]
  obtain ⟨L, hLS, hLmax⟩ :=
    S.exists_max_image (fun G => G.edgeFinset.card) hS
  have hLcond : K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
    simpa [S] using hLS
  refine ⟨L, hLcond.1, hLcond.2, ?_⟩
  intro M hLM hMplanar
  have hMcond : K ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M :=
    ⟨hLcond.1.trans hLM, hMplanar⟩
  have hMS : M ∈ S := by
    simp [S, hMcond]
  have hcard : M.edgeFinset.card ≤ L.edgeFinset.card := hLmax M hMS
  have hsub : L.edgeFinset ⊆ M.edgeFinset := SimpleGraph.edgeFinset_mono hLM
  have hedge : L.edgeFinset = M.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard
  exact SimpleGraph.edgeFinset_inj.mp hedge.symm

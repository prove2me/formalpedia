-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph__p2m_b1b3c510_149d_42bd_a072_8549c5a8211b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:12:03.256479+00:00
-- url     : https://prove2.me/submissions/6d36d191-9624-4482-a529-5989b2a0a50a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => K ≤ G ∧ HasPlanarDrawingOn G)
  have hS : S.Nonempty := by
    refine ⟨K, ?_⟩
    simp [S, hK]
  obtain ⟨L, hLmem, hLmax⟩ :=
    Finset.exists_max_image S (fun G : SimpleGraph V => G.edgeFinset.card) hS
  have hKL : K ≤ L := (Finset.mem_filter.mp hLmem).2.1
  have hDL : HasPlanarDrawingOn L := (Finset.mem_filter.mp hLmem).2.2
  refine ⟨L, hKL, hDL, ?_⟩
  intro M hLM hDM
  by_contra hML
  have hKM : K ≤ M := le_trans hKL hLM
  have hMmem : M ∈ S := by
    simp [S, hKM, hDM]
  have hlt : L.edgeFinset.card < M.edgeFinset.card := by
    apply Finset.card_lt_card
    exact SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr ⟨hLM, hML⟩
  exact (not_lt_of_ge (hLmax M hMmem)) hlt
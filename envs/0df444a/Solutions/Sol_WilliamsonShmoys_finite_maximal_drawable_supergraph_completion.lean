-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_drawable_supergraph_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:05:35.596801+00:00
-- url     : https://prove2.me/submissions/2d2cb00b-a4bc-4eba-8606-022d08c93856

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T) :
    ∃ K : SimpleGraph V,
      T ≤ K ∧ HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => T ≤ G ∧ HasPlanarDrawingOn G)
  have hS : S.Nonempty := by
    refine ⟨T, Finset.mem_filter.mpr ?_⟩
    simp [S, hT]
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) hS
  have hKT : T ≤ K := (Finset.mem_filter.mp hKmem).2.1
  have hKplanar : HasPlanarDrawingOn K := (Finset.mem_filter.mp hKmem).2.2
  refine ⟨K, hKT, hKplanar, ?_⟩
  intro L hKL hLplanar
  by_contra hneq
  have hlt : K < L := lt_of_le_of_ne hKL (Ne.symm hneq)
  have hTL : T ≤ L := le_trans hKT hKL
  have hLmem : L ∈ S := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hTL, hLplanar⟩
  have hcardlt : K.edgeFinset.card < L.edgeFinset.card :=
    Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  exact (not_lt_of_ge (hKmax L hLmem)) hcardlt
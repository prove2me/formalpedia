-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:02:01.000217+00:00
-- url     : https://prove2.me/submissions/e47af651-8062-4768-b1b6-926cb5a7eaa7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => L ≤ G ∧ HasPlanarDrawingOn G
  have h_candidates : candidates.Nonempty := by
    refine ⟨L, ?_⟩
    simp [candidates, hL]
  obtain ⟨M, hM_mem, hM_max⟩ :=
    Finset.exists_max_image candidates (fun G => G.edgeFinset.card) h_candidates
  have hM_props : L ≤ M ∧ HasPlanarDrawingOn M := by
    simpa [candidates] using hM_mem
  refine ⟨M, hM_props.1, hM_props.2, ?_⟩
  intro N hMN hNplanar
  by_contra hNM
  have hN_mem : N ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hM_props.1.trans hMN, hNplanar⟩
  have hproper : M.edgeFinset ⊂ N.edgeFinset := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · exact SimpleGraph.edgeFinset_mono hMN
    · intro heq
      apply hNM
      exact le_of_eq ((SimpleGraph.edgeFinset_inj.mp heq).symm)
  have hcard : M.edgeFinset.card < N.edgeFinset.card := Finset.card_lt_card hproper
  have hmax := hM_max N hN_mem
  exact (not_le_of_gt hcard) hmax
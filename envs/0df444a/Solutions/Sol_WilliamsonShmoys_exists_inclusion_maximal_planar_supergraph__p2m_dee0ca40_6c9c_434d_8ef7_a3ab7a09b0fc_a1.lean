-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_dee0ca40_6c9c_434d_8ef7_a3ab7a09b0fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:23:53.974772+00:00
-- url     : https://prove2.me/submissions/82b99d07-2df4-41c6-ad70-3e36311f8ba4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hR : HasPlanarDrawingOn R) :
    ∃ M : SimpleGraph V, R ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  classical
  letI : Finite (SimpleGraph V) :=
    Finite.of_injective (fun G : SimpleGraph V => G.edgeFinset) (by
      intro G H h
      exact (SimpleGraph.edgeFinset_inj).mp h)
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => R ≤ G ∧ HasPlanarDrawingOn G
  have candidates_nonempty : candidates.Nonempty := by
    refine ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨le_rfl, hR⟩
  obtain ⟨M, hM, hmax⟩ :=
    Finset.exists_max_image candidates (fun G => G.edgeFinset.card) candidates_nonempty
  refine ⟨M, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hM).2.1
  · exact (Finset.mem_filter.mp hM).2.2
  · intro N hMN hN
    have hRM : R ≤ M := (Finset.mem_filter.mp hM).2.1
    have hRN : R ≤ N := hRM.trans hMN
    have hNcandidates : N ∈ candidates := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hRN, hN⟩⟩
    by_contra hneq
    have hnot : ¬ N ≤ M := by
      intro hNM
      exact hneq (le_antisymm hNM hMN)
    have hstrict : M.edgeFinset ⊂ N.edgeFinset := by
      exact (SimpleGraph.edgeFinset_ssubset_edgeFinset).2 ⟨hMN, hnot⟩
    have hcard : M.edgeFinset.card < N.edgeFinset.card := Finset.card_lt_card hstrict
    have hbound := hmax N hNcandidates
    omega
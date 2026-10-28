-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph_v10_aux
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:04:35.67853+00:00
-- url     : https://prove2.me/submissions/25e66fb1-8db0-4f89-92df-0db0fdd40f4d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V =>
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => L ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨L, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_rfl, hL⟩
  let edgeCount : SimpleGraph V → ℕ := fun G => G.edgeFinset.card
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image S edgeCount hS
  refine ⟨M, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hM).2.1
  · exact (Finset.mem_filter.mp hM).2.2
  · intro N hMN hN
    by_contra hNM
    have hsub : M.edgeFinset ⊆ N.edgeFinset := by
      intro e he
      exact SimpleGraph.edgeFinset_mono hMN he
    have hnotSub : ¬ N.edgeFinset ⊆ M.edgeFinset := by
      intro hrev
      apply hNM
      intro u v huv
      have hEdge : s(u, v) ∈ N.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
      exact SimpleGraph.mem_edgeFinset.mp (hrev hEdge)
    have hcard : M.edgeFinset.card < N.edgeFinset.card :=
      Finset.card_lt_card ⟨hsub, hnotSub⟩
    have hNmem : N ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨le_trans ((Finset.mem_filter.mp hM).2.1) hMN, hN⟩
    have hmaxN := hmax N hNmem
    exact (Nat.not_lt_of_ge hmaxN) hcard
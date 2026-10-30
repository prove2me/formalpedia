-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_87706138_1b1b_4896_af61_3aff6d2d47f5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:45.922119+00:00
-- url     : https://prove2.me/submissions/8d992972-4005-46fb-a5bd-bce2afc54e75

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V, K ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => K ≤ G ∧ HasPlanarDrawingOn G
  have hKmem : K ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_rfl, hK⟩
  let T : Finset ℕ := S.image fun G => G.edgeFinset.card
  have hT : T.Nonempty := ⟨K.edgeFinset.card, Finset.mem_image.mpr ⟨K, hKmem, rfl⟩⟩
  let n : ℕ := T.max' hT
  have hn : n ∈ T := T.max'_mem hT
  obtain ⟨M, hMS, hMn⟩ := Finset.mem_image.mp hn
  have hM : K ≤ M ∧ HasPlanarDrawingOn M := (Finset.mem_filter.mp hMS).2
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro N hMN hN
  have hNS : N ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_trans hM.1 hMN, hN⟩
  have hNle : N.edgeFinset.card ≤ n :=
    T.le_max' _ (Finset.mem_image.mpr ⟨N, hNS, rfl⟩)
  have hMcard : M.edgeFinset.card = n := hMn
  by_contra hneq
  have hlt : M.edgeFinset.card < N.edgeFinset.card :=
    Finset.card_lt_card
      (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr
        (lt_of_le_of_ne hMN (Ne.symm hneq)))
  omega

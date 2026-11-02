-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_extension__p2m_625bb0fc_e249_4e4e_ba10_71dd29d5fb91_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:21:52.899669+00:00
-- url     : https://prove2.me/submissions/82669b4a-47ce-4848-9d8a-2dfba6db288b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => M ≤ G ∧ HasPlanarDrawingOn G
  have hMmem : M ∈ S := by
    simp [S, hM]
  have hS : S.Nonempty := ⟨M, hMmem⟩
  let C : Finset ℕ := S.image fun G => G.edgeFinset.card
  have hC : C.Nonempty := by
    exact ⟨M.edgeFinset.card, Finset.mem_image.mpr ⟨M, hMmem, rfl⟩⟩
  let c : ℕ := C.max' hC
  have hc_mem : c ∈ C := by
    exact Finset.max'_mem C hC
  obtain ⟨N, hNS, hNc⟩ := Finset.mem_image.mp hc_mem
  refine ⟨N, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hNS).2.1
  · exact (Finset.mem_filter.mp hNS).2.2
  · intro K hNK hKdraw
    have hMN : M ≤ N := (Finset.mem_filter.mp hNS).2.1
    have hKS : K ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hMN.trans hNK, hKdraw⟩
    have hKimage : K.edgeFinset.card ∈ C :=
      Finset.mem_image.mpr ⟨K, hKS, rfl⟩
    have hKle : K.edgeFinset.card ≤ c := by
      exact Finset.le_max' C _ hKimage
    by_contra hne
    have hsubset : N.edgeFinset ⊂ K.edgeFinset := by
      apply Finset.ssubset_iff_subset_ne.mpr
      exact ⟨SimpleGraph.edgeFinset_mono hNK,
        fun heq => hne (SimpleGraph.edgeFinset_inj.mp heq).symm⟩
    have hltN : N.edgeFinset.card < K.edgeFinset.card := Finset.card_lt_card hsubset
    have hlt : c < K.edgeFinset.card := by simpa [hNc] using hltN
    exact (Nat.not_lt_of_ge hKle) hlt
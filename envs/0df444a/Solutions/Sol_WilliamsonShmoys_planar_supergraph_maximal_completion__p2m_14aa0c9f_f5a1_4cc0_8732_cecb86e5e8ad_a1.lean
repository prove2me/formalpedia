-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_completion__p2m_14aa0c9f_f5a1_4cc0_8732_cecb86e5e8ad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:54:55.634795+00:00
-- url     : https://prove2.me/submissions/240eafcd-5471-40fa-b8f8-c7b3fa338b09

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists (fun K : SimpleGraph V =>
      G <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun K => G <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K)
  have hGmem : G ∈ S := by
    simp [S, hG]
  have hS : S.Nonempty := ⟨G, hGmem⟩
  obtain ⟨K, hKmem, hKmax⟩ := S.exists_max_image (fun K => K.edgeFinset.card) hS
  have hKprops : G <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K := by
    simpa [S] using hKmem
  have hGK : G <= K := hKprops.1
  have hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K := hKprops.2
  refine ⟨K, hGK, hKplanar, ?_⟩
  intro H hKH hHplanar
  have hHmem : H ∈ S := by
    simp [S, hGK.trans hKH, hHplanar]
  have hcard : H.edgeFinset.card <= K.edgeFinset.card := hKmax H hHmem
  by_contra hnot
  have hstrict : K.edgeFinset ⊂ H.edgeFinset := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · exact SimpleGraph.edgeFinset_mono hKH
    · intro heq
      apply hnot
      intro u v huv
      have hmemH : s(u, v) ∈ H.edgeFinset := by simpa using huv
      have hmemK : s(u, v) ∈ K.edgeFinset := by simpa [heq] using hmemH
      simpa using hmemK
  exact (not_le_of_gt (Finset.card_lt_card hstrict)) hcard
-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ddf70dfc_9e43_42b2_878d_a461f3516711_a6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:55:53.7752+00:00
-- url     : https://prove2.me/submissions/00dc8c1c-361c-444a-9040-2610694ea859

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) ∧
      (letI : DecidableRel H.Adj := Classical.decRel _
       letI : DecidableRel K.Adj := Classical.decRel _
       H.edgeFinset.card ≤ K.edgeFinset.card) := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel _
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun K => H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  have h_candidates : candidates.Nonempty := by
    refine ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ H, ?_⟩⟩
    exact ⟨le_rfl, hH⟩
  obtain ⟨K, hK_mem, hK_max⟩ :=
    candidates.exists_max_image (fun G => G.edgeFinset.card) h_candidates
  have hK : H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K :=
    (Finset.mem_filter.mp hK_mem).2
  refine ⟨K, hK.1, hK.2, ?_, ?_⟩
  · intro L hKL hL
    have hL_mem : L ∈ candidates := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ L, ⟨hK.1.trans hKL, hL⟩⟩
    have hcard_le : L.edgeFinset.card ≤ K.edgeFinset.card := hK_max L hL_mem
    have hsub : K.edgeFinset ⊆ L.edgeFinset := by
      exact SimpleGraph.edgeFinset_mono hKL
    have hcard_rev : K.edgeFinset.card ≤ L.edgeFinset.card := Finset.card_le_card hsub
    have heq_edges : K.edgeFinset = L.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsub hcard_le
    apply SimpleGraph.ext
    funext u
    funext v
    apply propext
    constructor
    · intro huv
      have hv_mem : s(u, v) ∈ L.edgeFinset := by
        simp [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet, huv]
      have hk_mem : s(u, v) ∈ K.edgeFinset := by
        simpa [heq_edges] using hv_mem
      simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet] using hk_mem
    · intro huv; exact hKL huv
  · exact hK_max H (by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ H, ⟨le_rfl, hH⟩⟩)

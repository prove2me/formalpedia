-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_c985394f_ff9a_4827_826c_d7a45e5d518a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:30:26.038727+00:00
-- url     : https://prove2.me/submissions/dc3320b2-b620-40b9-89c3-8e4738081d99

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) :
    letI : forall H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
    exists N : SimpleGraph V,
      (forall u v, G.Adj u v -> N.Adj u v) ∧
      HasPlanarDrawingOn N ∧
      forall H : SimpleGraph V,
        (forall u v, N.Adj u v -> H.Adj u v) ->
        HasPlanarDrawingOn H -> H = N := by
  classical
  letI : forall H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun H =>
      (forall u v, G.Adj u v -> H.Adj u v) ∧ HasPlanarDrawingOn H
  have hG : G ∈ candidates := by
    simp [candidates, hdraw]
  obtain ⟨N, hNmem, hNmax⟩ :=
    Finset.exists_max_image candidates (fun H => H.edgeFinset.card) ⟨G, hG⟩
  refine ⟨N, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hNmem).2.1
  · exact (Finset.mem_filter.mp hNmem).2.2
  · intro H hNH hHdraw
    have hHmem : H ∈ candidates := by
      apply Finset.mem_filter.mpr
      constructor
      · simp
      · constructor
        · intro u v huv
          exact hNH u v ((Finset.mem_filter.mp hNmem).2.1 u v huv)
        · exact hHdraw
    have hle : H.edgeFinset.card ≤ N.edgeFinset.card := hNmax H hHmem
    by_contra hneq
    have hsub : N.edgeFinset ⊆ H.edgeFinset :=
      SimpleGraph.edgeFinset_subset_edgeFinset.mpr hNH
    have hne : N.edgeFinset ≠ H.edgeFinset := by
      intro he
      exact hneq (SimpleGraph.edgeFinset_inj.mp he).symm
    have hss : N.edgeFinset ⊂ H.edgeFinset :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    exact (not_le_of_gt (Finset.card_lt_card hss)) hle
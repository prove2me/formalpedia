-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_maximal_extension__p2m_92aefffa_7fe2_4e94_9c0b_6e84d250c255_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T02:30:19.543346+00:00
-- url     : https://prove2.me/submissions/ec282e17-e26f-4816-ac08-5387b4324847

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V, N ≤ M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       letI : DecidableRel M.Adj := Classical.decRel M.Adj
       N.edgeFinset.card ≤ M.edgeFinset.card) ∧
      ∀ M' : SimpleGraph V, HasPlanarDrawingOn M' → M ≤ M' → M' = M := by
  classical
  let p : SimpleGraph V → Prop := fun G => N ≤ G ∧ HasPlanarDrawingOn G
  have hp : ∃ G : SimpleGraph V, p G := ⟨N, le_rfl, hN⟩
  obtain ⟨M, hMdec, hM⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 hp
  have hMedge :
      @SimpleGraph.edgeFinset V M
          (@SimpleGraph.fintypeEdgeSet V M Sym2.instFintype hMdec) =
        @SimpleGraph.edgeFinset V M
          (@SimpleGraph.fintypeEdgeSet V M Sym2.instFintype
            (Classical.decRel M.Adj)) := by
    ext e
    simp
  have hNM : N ≤ M := hM.1.1
  have hMplanar : HasPlanarDrawingOn M := hM.1.2
  refine ⟨M, hNM, hMplanar, ?_, ?_⟩
  · have hbound := hM.2 ⟨le_rfl, hN⟩
    change N.edgeFinset.card ≤
      (@SimpleGraph.edgeFinset V M
        (@SimpleGraph.fintypeEdgeSet V M Sym2.instFintype hMdec)).card at hbound
    rw [hMedge] at hbound
    exact hbound
  · intro M' hM' hMM'
    have hNM' : N ≤ M' := le_trans hNM hMM'
    have hbound := hM.2 ⟨hNM', hM'⟩
    have hcount : M'.edgeFinset.card ≤ M.edgeFinset.card := hbound
    have hEdges : M.edgeFinset = M'.edgeFinset :=
      Finset.eq_of_subset_of_card_le
        (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hMM') hcount
    exact (SimpleGraph.edgeFinset_inj.mp hEdges).symm
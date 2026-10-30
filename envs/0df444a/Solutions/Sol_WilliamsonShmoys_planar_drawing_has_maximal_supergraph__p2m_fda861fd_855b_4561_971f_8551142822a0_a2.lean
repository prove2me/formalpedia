-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_fda861fd_855b_4561_971f_8551142822a0_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:43:53.399983+00:00
-- url     : https://prove2.me/submissions/23b54cb8-1b98-41a7-981b-1a3c65f0296f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P.edgeSet ⊆ Q.edgeSet ∧ HasPlanarDrawingOn Q ∧
      (∀ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet → HasPlanarDrawingOn R → R = Q) := by
  classical
  let S : Set (SimpleGraph V) := {Q | P ≤ Q ∧ HasPlanarDrawingOn Q}
  have hfinite : S.Finite := Set.toFinite S
  have hnonempty : S.Nonempty := ⟨P, by simp [S, hDraw]⟩
  obtain ⟨Q, hQmax⟩ := hfinite.exists_maximal hnonempty
  have hPQ : P ≤ Q := hQmax.1.1
  have hQdraw : HasPlanarDrawingOn Q := hQmax.1.2
  refine ⟨Q, SimpleGraph.edgeSet_subset_edgeSet.mpr hPQ, hQdraw, ?_⟩
  intro R hQR hRdraw
  have hQRle : Q ≤ R := SimpleGraph.edgeSet_subset_edgeSet.mp hQR
  have hPR : P ≤ R := hPQ.trans hQRle
  have hRmem : R ∈ S := ⟨hPR, hRdraw⟩
  have hle : R ≤ Q := hQmax.2 hRmem hQRle
  exact le_antisymm hle hQRle

-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a49ca777_83c4_4524_a92f_84ff8c99b9bc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:50:02.032199+00:00
-- url     : https://prove2.me/submissions/e07b17d9-3d54-415f-8025-5f8d2640dc6e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
      (letI : DecidableRel G.Adj := Classical.decRel _
       letI : DecidableRel H.Adj := Classical.decRel _
       G.edgeFinset.card ≤ H.edgeFinset.card) := by
  classical
  let P : Set (SimpleGraph V) := {K | G ≤ K ∧ HasPlanarDrawingOn K}
  have hPfinite : P.Finite := Set.toFinite P
  obtain ⟨H, hHP, hmax⟩ :=
    Set.exists_max_image P (fun K : SimpleGraph V => K.edgeFinset.card) hPfinite
      ⟨G, le_rfl, hG⟩
  refine ⟨H, hHP.1, hHP.2, ?_, ?_⟩
  · intro K hHK hK
    have hKP : K ∈ P := ⟨hHP.1.trans hHK, hK⟩
    rcases lt_or_eq_of_le hHK with hlt | heq
    · have hcard : H.edgeFinset.card < K.edgeFinset.card := by
        apply Finset.card_lt_card
        exact (SimpleGraph.edgeFinset_ssubset_edgeFinset).2 hlt
      have hbound := hmax K hKP
      omega
    · exact heq.symm
  · letI : DecidableRel G.Adj := Classical.decRel _
    letI : DecidableRel H.Adj := Classical.decRel _
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHP.1)
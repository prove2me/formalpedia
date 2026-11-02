-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_maximal_extension__p2m_637d8540_4fa2_4bdf_8eaf_997caf9c33c1_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:09:04.720725+00:00
-- url     : https://prove2.me/submissions/faab9af4-b7b2-4e7f-b5b4-7f5736b395bd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N) :
    ∃ (P : SimpleGraph V), N ≤ P ∧ HasPlanarDrawingOn P ∧
      (∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q = P) := by
  classical
  obtain ⟨P, hNP, hmax⟩ :=
    @Finite.exists_le_maximal (SimpleGraph V) _ _
      (fun G => N ≤ G ∧ HasPlanarDrawingOn G) N ⟨le_rfl, hN⟩
  refine ⟨P, hNP, hmax.prop.2, ?_⟩
  intro Q hPQ hQ
  have hQpred : N ≤ Q ∧ HasPlanarDrawingOn Q := ⟨hNP.trans hPQ, hQ⟩
  by_contra hne
  exact hmax.not_prop_of_gt (lt_of_le_of_ne hPQ (Ne.symm hne)) hQpred
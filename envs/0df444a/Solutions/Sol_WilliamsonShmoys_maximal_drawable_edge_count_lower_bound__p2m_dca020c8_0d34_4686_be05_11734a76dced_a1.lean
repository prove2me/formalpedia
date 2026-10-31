-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_dca020c8_0d34_4686_be05_11734a76dced_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:27:46.735766+00:00
-- url     : https://prove2.me/submissions/397ce3be-20d9-4409-b586-a87b3e831b08

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn Q)
    (hMax : ∀ R : SimpleGraph V, Q ≤ R → HasPlanarDrawingOn R → R ≤ Q)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ Q.edgeSet.ncard := by
  obtain ⟨R, hQR, hRDraw, hRCard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1
      Q hDraw hV
  have hRQ : R ≤ Q := hMax R hQR hRDraw
  have hQRCard :=
    WilliamsonShmoys.edgeSet_ncard_mono__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1 Q R hQR
  have hRQCard :=
    WilliamsonShmoys.edgeSet_ncard_mono__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1 R Q hRQ
  omega
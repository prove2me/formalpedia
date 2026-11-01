-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_face_count_certificate__p2m_8700ddcb_5e54_440d_86e0_a8d22ebd60f0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:42:29.180482+00:00
-- url     : https://prove2.me/submissions/90c05733-dbf3-4c8b-bb53-258a87d61765
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawing_euler_face_count__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawing_simple_edge_bound__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
import Theorems.Thm_WilliamsonShmoys_nat_face_length_distribution__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : Nat, ∃ faceLength : Fin f → Nat,
      Fintype.card V + f =
          (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 ∧
        (∑ i : Fin f, faceLength i) =
          2 * (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) ∧
        ∀ i : Fin f, 3 ≤ faceLength i := by
  obtain ⟨f, hfpos, hEuler⟩ :=
    WilliamsonShmoys.planarDrawing_euler_face_count__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
      G dG hG hConn hcard
  have hEdge :=
    WilliamsonShmoys.planarDrawing_simple_edge_bound__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
      G dG hG hConn hcard
  obtain ⟨faceLength, hsum, hlen⟩ :=
    WilliamsonShmoys.nat_face_length_distribution__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
      (Fintype.card V) (letI : DecidableRel G.Adj := dG; G.edgeFinset.card)
      f hEuler hEdge hfpos
  exact ⟨f, faceLength, hEuler, hsum, hlen⟩
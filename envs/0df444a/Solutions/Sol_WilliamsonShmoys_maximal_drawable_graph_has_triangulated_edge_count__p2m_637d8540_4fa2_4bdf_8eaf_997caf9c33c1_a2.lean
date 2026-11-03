-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_triangulated_edge_count__p2m_637d8540_4fa2_4bdf_8eaf_997caf9c33c1_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:50:04.073274+00:00
-- url     : https://prove2.me/submissions/bfd94382-cbc7-4bec-a8f0-3bf6445b73d3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_extension__p2m_4b104b32_56a0_4b02_b537_5e9d1339dc2d_a2
open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) [hPdec : DecidableRel P.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hP : HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q = P) :
    P.edgeFinset.card + 6 = 3 * Fintype.card V := by
  obtain ⟨Q, hQdec, hPQ, hQ, hcount⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulated_extension__p2m_4b104b32_56a0_4b02_b537_5e9d1339dc2d_a2
      P hcard hP
  letI : DecidableRel Q.Adj := hQdec
  have hQP : Q = P := hmax Q hPQ hQ
  cases hQP
  have hdeceq : hQdec = hPdec := Subsingleton.elim _ _
  rw [hdeceq] at hcount
  exact hcount
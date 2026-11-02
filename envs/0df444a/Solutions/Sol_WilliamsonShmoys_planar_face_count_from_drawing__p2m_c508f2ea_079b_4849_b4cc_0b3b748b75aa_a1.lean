-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_from_drawing__p2m_c508f2ea_079b_4849_b4cc_0b3b748b75aa_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:39:39.007578+00:00
-- url     : https://prove2.me/submissions/a6e40272-5009-468a-872b-70e9d356cd7b

import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a1
import Theorems.Thm_WilliamsonShmoys_planar_face_bound_from_euler_and_edge_bound__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : Nat.le 3 (Fintype.card V)) :
    Exists fun f : Nat => And
      (H.edgeFinset.card + 2 = Fintype.card V + f)
      (3 * f <= 2 * H.edgeFinset.card) := by
  have he :=
    WilliamsonShmoys.planar_drawing_euler__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a1
      H dH hconn hH
  cases he with
  | intro f heuler =>
    have hbound :=
      WilliamsonShmoys.planar_drawing_edge_bound__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a1
        H dH hconn hH hn
    exact Exists.intro f (And.intro heuler
      (WilliamsonShmoys.planar_face_bound_from_euler_and_edge_bound__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a2
        H.edgeFinset.card (Fintype.card V) f heuler hbound))
-- Prove2me | solution 1 for WilliamsonShmoys.planar_euler_face_incidence_bound__p2m_5594ab01_5507_4608_93d6_8bce1469fe90_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:51:53.015181+00:00
-- url     : https://prove2.me/submissions/f9b395db-2735-4e8b-9c96-6faf334deac8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_7c073d05_f8af_49af_8234_528c2585cbfc_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∀ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 →
      3 * f ≤ 2 * H.edgeFinset.card := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  intro f heuler
  obtain ⟨K, hsub, _hK, htri⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_7c073d05_f8af_49af_8234_528c2585cbfc_a1
      H hconn hH hcard
  have hmono : H.edgeFinset.card ≤ K.edgeFinset.card := Finset.card_le_card hsub
  nlinarith [heuler, htri, hmono]
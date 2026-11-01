-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count__p2m_dbfda827_a827_4911_8354_de916f36b6c0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:10.427855+00:00
-- url     : https://prove2.me/submissions/18cbcb98-13bb-4374-8da1-d01696e866f3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeFinset.card + 2 := by
  letI : DecidableRel K.Adj := dK
  have hle := hconn.card_vert_le_card_edgeSet_add_one
  simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at hle
  refine ⟨K.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega
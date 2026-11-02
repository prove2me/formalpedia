-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_euler_face_count__p2m_75c1dbe5_597b_4ab5_bcaf_dc768f4756d8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:19:13.38464+00:00
-- url     : https://prove2.me/submissions/53b2854b-eb88-41ce-b50f-f558a6611fd6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) (hconn : U.Connected) :
    (letI : DecidableRel U.Adj := dU
     ∃ f : Nat,
       Fintype.card V + f = U.edgeFinset.card + 2) := by
  letI : DecidableRel U.Adj := dU
  have hcard : Fintype.card V ≤ U.edgeFinset.card + 1 := by
    simpa [SimpleGraph.edgeFinset_card] using
      hconn.card_vert_le_card_edgeSet_add_one
  refine ⟨U.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega
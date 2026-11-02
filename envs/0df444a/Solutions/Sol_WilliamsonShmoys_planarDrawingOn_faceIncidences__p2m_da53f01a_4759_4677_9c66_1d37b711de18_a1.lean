-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_faceIncidences__p2m_da53f01a_4759_4677_9c66_1d37b711de18_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:56:07.021051+00:00
-- url     : https://prove2.me/submissions/cbedd4dd-0b51-4625-9e1c-e42f2faf4693

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hn : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f =
      (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) + 2) :
    ∃ i : ℕ,
      2 * (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) ≤ i ∧
      3 * f ≤ i := by
  refine ⟨2 * (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) + 3 * f, ?_, ?_⟩
  · omega
  · omega
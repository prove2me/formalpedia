-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.neighborIncidenceCount_univ
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T07:52:05.772027+00:00
-- url     : https://prove2.me/submissions/4aa6e03a-1e92-4b5c-aa5e-1a0f17589e3d

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
theorem solution
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : ZMod ell) :
    neighborIncidenceCount twistSample Finset.univ u =
      2 * typeCount := by
  classical
  simp only [neighborIncidenceCount, Finset.mem_univ, ↓reduceIte]
  simp [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  ring

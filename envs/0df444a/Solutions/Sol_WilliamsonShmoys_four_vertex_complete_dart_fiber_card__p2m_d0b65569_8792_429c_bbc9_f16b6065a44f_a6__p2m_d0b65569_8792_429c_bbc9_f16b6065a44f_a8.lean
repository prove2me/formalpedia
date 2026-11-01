-- Prove2me | solution 1 for WilliamsonShmoys.four_vertex_complete_dart_fiber_card__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:00.097924+00:00
-- url     : https://prove2.me/submissions/441e2950-b80e-4fbc-9046-bd150bc1b27e

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    [DecidableRel H.Adj]
    (hV : Fintype.card V = 4)
    (hcomplete : forall u v : V, Not (u = v) -> H.Adj u v) (v : V) :
    Fintype.card {a : H.Dart // a.fst = v} = 3 := by
  classical
  let e : Equiv {a : H.Dart // a.fst = v} {w : V // Not (w = v)} :=
    { toFun := fun a => Subtype.mk a.1.snd (by
        intro h
        have hadj := a.1.adj
        rw [a.2, h] at hadj
        exact H.irrefl hadj)
      invFun := fun w =>
        Subtype.mk (SimpleGraph.Dart.mk (v, w.1) (hcomplete v w.1 (by
          intro hvw
          exact w.2 hvw.symm))) rfl
      left_inv := by
        intro a
        apply Subtype.ext
        apply SimpleGraph.Dart.ext
        apply Prod.ext
        exact a.2.symm
        rfl
      right_inv := by
        intro w
        apply Subtype.ext
        rfl }
  calc
    Fintype.card {a : H.Dart // a.fst = v} = Fintype.card {w : V // Not (w = v)} :=
      Fintype.card_congr e
    _ = 3 := by
      rw [Fintype.card_subtype_compl (p := fun w : V => w = v)]
      simp [hV]
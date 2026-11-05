-- Prove2me | solution 1 for WilliamsonShmoys.four_vertex_complete_dart_fiber_card__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:25:38.321206+00:00
-- url     : https://prove2.me/submissions/5d40639b-4fb5-47f1-a015-70b7a0bae6d7

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    [DecidableRel H.Adj]
    (hV : Fintype.card V = 4)
    (hcomplete : forall u v : V, u ≠ v -> H.Adj u v) (v : V) :
    Fintype.card {a : H.Dart // a.fst = v} = 3 := by
  classical
  let e : {a : H.Dart // a.fst = v} ≃ {w : V // w ≠ v} :=
    { toFun := fun a => ⟨a.1.snd, fun h =>
          (SimpleGraph.Dart.fst_ne_snd a.1) (a.2.trans h.symm)⟩
      invFun := fun w => ⟨⟨(v, w.1), hcomplete v w.1 (Ne.symm w.2)⟩, rfl⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply SimpleGraph.Dart.ext
        apply Prod.ext
        · exact a.2.symm
        · rfl
      right_inv := by
        intro w
        apply Subtype.ext
        rfl }
  have hne : Fintype.card {w : V // w ≠ v} = 3 := by
    rw [Fintype.card_subtype_compl (p := fun w : V => w = v)]
    rw [Fintype.card_subtype_eq v]
    omega
  exact (Fintype.card_congr e).trans hne

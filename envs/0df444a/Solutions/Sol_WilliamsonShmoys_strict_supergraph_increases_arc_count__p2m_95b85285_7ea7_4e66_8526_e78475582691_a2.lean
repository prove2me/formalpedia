-- Prove2me | solution 1 for WilliamsonShmoys.strict_supergraph_increases_arc_count__p2m_95b85285_7ea7_4e66_8526_e78475582691_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:18:12.441003+00:00
-- url     : https://prove2.me/submissions/1de6d8db-262a-470c-90f6-e53567180dd1

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K H : SimpleGraph V)
    (hKH : K ≤ H) (hnot : ¬ H ≤ K) :
    Nat.card {p : V × V // K.Adj p.1 p.2} <
      Nat.card {p : V × V // H.Adj p.1 p.2} := by
  classical
  rw [SimpleGraph.le_iff_adj] at hnot
  push_neg at hnot
  obtain ⟨x, y, hHxy, hKxy⟩ := hnot
  let f : {p : V × V // K.Adj p.1 p.2} →
      {p : V × V // H.Adj p.1 p.2} := fun p =>
    ⟨p.val, (SimpleGraph.le_iff_adj.mp hKH) p.val.1 p.val.2 p.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z => z.1) hab
  let b : {p : V × V // H.Adj p.1 p.2} := ⟨(x, y), hHxy⟩
  have hb : b ∉ Set.range f := by
    rintro ⟨p, hp⟩
    have hval : p.val = (x, y) := congrArg (fun z => z.1) hp
    have hK' : K.Adj x y := by
      simpa [hval] using p.property
    exact hKxy hK'
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem f hf hb
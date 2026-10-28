-- Prove2me | solution 1 for WilliamsonShmoys.strict_adjacency_pair_count_of_strict_graph_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:17:43.409984+00:00
-- url     : https://prove2.me/submissions/d98637e8-9eff-49de-bada-39c7e65d7f44

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V) (hKL : LE.le K L) (hneq : L ≠ K) :
    Nat.card {p : V × V // K.Adj p.1 p.2} <
      Nat.card {p : V × V // L.Adj p.1 p.2} := by
  classical
  let f : {p : V × V // K.Adj p.1 p.2} → {p : V × V // L.Adj p.1 p.2} :=
    fun p => ⟨p.1, hKL p.2⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun r : {p : V × V // L.Adj p.1 p.2} => r.1) hpq
  have hns : ¬ Function.Surjective f := by
    intro hs
    apply hneq
    ext u v
    constructor
    · intro huv
      obtain ⟨p, hp⟩ := hs ⟨(u, v), huv⟩
      have hval : p.1 = (u, v) := congrArg (fun r : {p : V × V // L.Adj p.1 p.2} => r.1) hp
      rcases Prod.mk.inj hval with ⟨rfl, rfl⟩
      exact p.2
    · intro huv
      exact hKL huv
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_lt_of_injective_not_surjective f hf hns)
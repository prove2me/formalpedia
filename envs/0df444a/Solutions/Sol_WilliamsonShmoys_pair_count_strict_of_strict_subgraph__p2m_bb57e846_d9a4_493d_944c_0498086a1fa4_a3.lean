-- Prove2me | solution 1 for WilliamsonShmoys.pair_count_strict_of_strict_subgraph__p2m_bb57e846_d9a4_493d_944c_0498086a1fa4_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:18:17.91522+00:00
-- url     : https://prove2.me/submissions/b1cbbad6-31f2-467d-bf60-562714dd16e5

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L M : SimpleGraph V) (hLM : L ≤ M) (hML : ¬ M ≤ L) :
    Nat.card {p : V × V // L.Adj p.1 p.2} <
      Nat.card {p : V × V // M.Adj p.1 p.2} := by
  classical
  let f : {p : V × V // L.Adj p.1 p.2} → {p : V × V // M.Adj p.1 p.2} :=
    fun p => ⟨p.1, hLM p.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    simpa [f] using
      congrArg (fun z : {p : V × V // M.Adj p.1 p.2} => z.1) hab
  have hns : ¬ Function.Surjective f := by
    intro hsurj
    apply hML
    intro a b hab
    obtain ⟨q, hq⟩ := hsurj ⟨(a, b), hab⟩
    have hval : q.1 = (a, b) := congrArg Subtype.val hq
    have hqL : L.Adj q.1.1 q.1.2 := q.2
    rw [hval] at hqL
    exact hqL
  simpa [Nat.card_eq_fintype_card] using
    (Fintype.card_lt_of_injective_not_surjective f hf hns)
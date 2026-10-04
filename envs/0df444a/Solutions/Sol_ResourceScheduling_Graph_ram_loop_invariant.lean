-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_loop_invariant
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:42:36.607857+00:00
-- url     : https://prove2.me/submissions/e4b8df76-8853-40fd-87fd-6e6d6d8a6375

import Definitions.Def_ResourceScheduling_Graph_RAMBudget

set_option autoImplicit false
open ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (v : V) (p : RAMCode V)
    (B n : ℕ) (I : ℕ → RAMState V → Prop) (s : RAMState V)
    (hs : RAMBound B s) (hn : s.val v = n) (hi : I 0 s)
    (hstep : ∀ k < n, ∀ x, I k x →
      p.Bounded B (x.set v (x.val v - 1)) ∧ I (k + 1) (p.eval (x.set v (x.val v - 1)))) :
    (RAMCode.loop v p).Bounded B s ∧ I n ((RAMCode.loop v p).eval s) := by
  let f := fun x : RAMState V => p.eval (x.set v (x.val v - 1))
  have hall : ∀ k ≤ n, I k ((f^[k]) s) := by
    intro k hk
    induction k with
    | zero => exact hi
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (hstep k (by omega) _ (ih (by omega))).2
  refine ⟨⟨hs, ?_⟩, ?_⟩
  · intro k hk
    exact (hstep k (by omega) _ (hall k (by omega))).1
  · simpa only [RAMCode.eval, hn] using hall n le_rfl

#print axioms solution

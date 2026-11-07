-- Prove2me | solution 1 for QEC.Coding.BitTuring.iterate_stackSize_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:01:48.60938+00:00
-- url     : https://prove2.me/submissions/1736e14a-b5bd-4598-b240-15721013ebc8

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_QEC_Coding_BitTuring_StackGrowth
import Theorems.Thm_QEC_Coding_BitTuring_step_stackSize_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring
open Turing
open scoped BigOperators
namespace QEC.Coding.BitTuring
theorem _root_.solution {K Λ σ : Type} [Fintype K] [DecidableEq K] [Fintype Λ]
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (n : ℕ)
    (c c' : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (hRun : (fun x => x.bind (TM2.step M))^[n] (some c) = some c') :
    stackSize c'.stk ≤ stackSize c.stk + n * programPushes M := by
  induction n generalizing c with
  | zero =>
      have h : c = c' := Option.some.inj hRun
      subst c'
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hRun
      cases hStep : TM2.step M c with
      | none =>
          simp only [Option.bind_some, hStep] at hRun
          have hn : (fun x => x.bind (TM2.step M))^[n] none = none := by
            exact Function.iterate_fixed (f := fun x : Option (TM2.Cfg (fun _ : K => Bool) Λ σ) => x.bind (TM2.step M)) rfl n
          rw [hn] at hRun
          cases hRun
      | some c₁ =>
          simp only [Option.bind_some, hStep] at hRun
          have hi := ih c₁ hRun
          have hs := step_stackSize_le M c c₁ hStep
          calc
            stackSize c'.stk ≤ stackSize c₁.stk + n * programPushes M := hi
            _ ≤ stackSize c.stk + programPushes M + n * programPushes M := Nat.add_le_add_right hs _
            _ = stackSize c.stk + (n + 1) * programPushes M := by ring
end QEC.Coding.BitTuring

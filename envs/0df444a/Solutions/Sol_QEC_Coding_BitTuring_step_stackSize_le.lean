-- Prove2me | solution 1 for QEC.Coding.BitTuring.step_stackSize_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:01:09.95326+00:00
-- url     : https://prove2.me/submissions/ebf73b40-c3d1-4f44-b4dc-7f075bfe99ea

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_QEC_Coding_BitTuring_StackGrowth
import Theorems.Thm_QEC_Coding_BitTuring_stepAux_stackSize_le
import Theorems.Thm_QEC_Coding_BitTuring_pushes_le_programPushes

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring
open Turing
open scoped BigOperators
namespace QEC.Coding.BitTuring
theorem _root_.solution {K Λ σ : Type} [Fintype K] [DecidableEq K] [Fintype Λ]
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (c c' : TM2.Cfg (fun _ : K => Bool) Λ σ) (hstep : TM2.step M c = some c') :
    stackSize c'.stk ≤ stackSize c.stk + programPushes M := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at hstep
  | some l =>
      have hc : TM2.stepAux (M l) v S = c' := Option.some.inj hstep
      rw [← hc]
      exact (stepAux_stackSize_le _ _ _).trans
        (Nat.add_le_add_left (pushes_le_programPushes M l) _)
end QEC.Coding.BitTuring

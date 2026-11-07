-- Prove2me | solution 1 for QEC.Coding.BitTuring.stepAux_stackSize_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:00:39.566624+00:00
-- url     : https://prove2.me/submissions/4473405a-c219-49f4-98dd-3c894ec9f2ad

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_QEC_Coding_BitTuring_StackGrowth
import Theorems.Thm_QEC_Coding_BitTuring_stackSize_push
import Theorems.Thm_QEC_Coding_BitTuring_stackSize_pop

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring
open Turing
open scoped BigOperators
namespace QEC.Coding.BitTuring
theorem _root_.solution {K Λ σ : Type} [Fintype K] [DecidableEq K]
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ) (tapes : K → List Bool) :
    stackSize (TM2.stepAux q v tapes).stk ≤ stackSize tapes + pushes q := by
  induction q generalizing v tapes with
  | push k f q ih =>
      simpa only [TM2.stepAux, pushes, stackSize_push, Nat.add_assoc, Nat.add_comm 1]
        using ih v (Function.update tapes k (f v :: tapes k))
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
      exact (ih _ _).trans (Nat.add_le_add_right (stackSize_pop tapes k) _)
  | load f q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases h : f v
      · simpa [TM2.stepAux, h, pushes] using (ih₂ v tapes).trans
          (Nat.add_le_add_left (Nat.le_max_right (pushes q₁) (pushes q₂)) _)
      · simpa [TM2.stepAux, h, pushes] using (ih₁ v tapes).trans
          (Nat.add_le_add_left (Nat.le_max_left (pushes q₁) (pushes q₂)) _)
  | goto f => exact le_refl _
  | halt => exact le_refl _
end QEC.Coding.BitTuring

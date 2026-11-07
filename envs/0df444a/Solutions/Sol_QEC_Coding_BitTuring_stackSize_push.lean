-- Prove2me | solution 1 for QEC.Coding.BitTuring.stackSize_push
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:59:44.564196+00:00
-- url     : https://prove2.me/submissions/a0234fe9-a98f-49d1-9726-fd8c3e2d2b39

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_QEC_Coding_BitTuring_StackGrowth
import Theorems.Thm_QEC_Coding_BitTuring_stackSize_update

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring
open Turing
open scoped BigOperators
namespace QEC.Coding.BitTuring
theorem _root_.solution {K : Type} [Fintype K] [DecidableEq K]
    (tapes : K → List Bool) (k : K) (bit : Bool) :
    stackSize (Function.update tapes k (bit :: tapes k)) = stackSize tapes + 1 := by
  have h := stackSize_update tapes k (bit :: tapes k)
  simp only [List.length_cons] at h
  omega
end QEC.Coding.BitTuring

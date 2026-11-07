-- Prove2me | solution 1 for QEC.Coding.BitTuring.stackSize_pop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:59:49.43278+00:00
-- url     : https://prove2.me/submissions/bed945df-ae49-4881-a020-9da7f821104f

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
    (tapes : K → List Bool) (k : K) :
    stackSize (Function.update tapes k (tapes k).tail) ≤ stackSize tapes := by
  have h := stackSize_update tapes k (tapes k).tail
  have ht : (tapes k).tail.length ≤ (tapes k).length := by simp only [List.length_tail]; omega
  omega
end QEC.Coding.BitTuring

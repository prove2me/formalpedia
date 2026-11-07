-- Prove2me | solution 1 for QEC.Coding.BitTuring.stackSize_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:52:06.224591+00:00
-- url     : https://prove2.me/submissions/81015684-d1b4-4ecb-a202-a8467785724e

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_QEC_Coding_BitTuring_StackGrowth

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring
open Turing
open scoped BigOperators
namespace QEC.Coding.BitTuring
theorem _root_.solution {K : Type} [Fintype K] [DecidableEq K]
    (tapes : K → List Bool) (k : K) (value : List Bool) :
    stackSize (Function.update tapes k value) + (tapes k).length =
      stackSize tapes + value.length := by
  have hu : (fun j => (Function.update tapes k value j).length) =
      Function.update (fun j => (tapes j).length) k value.length := by
    funext j
    by_cases hj : j = k <;> simp [hj]
  simp only [stackSize, hu]
  rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hh := Finset.sum_erase_add Finset.univ (fun j => (tapes j).length) (Finset.mem_univ k)
  rw [Finset.sdiff_singleton_eq_erase]
  omega
end QEC.Coding.BitTuring

-- Prove2me | solution 1 for P2M_DeciSigma1_Holes_Tail_getElem__pumpFactor_ge_c1284156d4c1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:52:25.54625+00:00
-- url     : https://prove2.me/submissions/6d046636-e376-46f0-81cb-8332ce2bd57b

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_DeciSigma1_Holes_Tail_le_length_pow_loop
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable {x : List α} {c c' L : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (hcc : c < c') (hc' : c' ≤ x.length) {p : ℕ} (hc : c ≤ p)
    (hp : p < c + L) : (pumpFactor x c c' L)[p]? = x[c + (p - c) % (c' - c)]? := by
  have hlen := le_length_pow_loop hcc hc' L
  unfold pumpFactor
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take, min_eq_left (by omega : c ≤ x.length)]
  rw [List.getElem?_take_of_lt (by omega), Words.getElem?_pow
    (loop_ne_nil hcc hc') (by omega), length_loop hc',
    List.getElem?_take_of_lt (Nat.mod_lt _ (by omega)), List.getElem?_drop]
end DeciSigma1.Holes.Tail

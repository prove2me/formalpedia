-- Prove2me | solution 1 for Parikh.representative_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:09.436288+00:00
-- url     : https://prove2.me/submissions/3d673e2d-c3a1-48c0-b3a7-208bca9a1af5

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization

set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [DecidableEq T] (alphabet : AlphabetOrder T) (v : Vector T) :
    counts (representative alphabet v) = v := by
  funext a
  change List.count a ((alphabet.letters.map fun b => List.replicate (v b) b).flatten) = v a
  rw [List.count_flatten, List.map_map]
  have hzero : ∀ b, b ≠ a → b ∈ alphabet.letters →
      (List.count a ∘ fun b => List.replicate (v b) b) b = 0 := by
    intro b hba _
    simp [List.count_replicate, hba]
  rw [List.sum_map_eq_nsmul_single a _ hzero,
    List.count_eq_one_of_mem alphabet.nodup (alphabet.complete a)]
  simp
end Parikh

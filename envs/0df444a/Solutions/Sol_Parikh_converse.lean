-- Prove2me | solution 1 for Parikh.converse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:55:58.383798+00:00
-- url     : https://prove2.me/submissions/a248713d-1266-4061-a6d3-aa028d10ab4a

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Theorems.Thm_Parikh_witnessExpression_correct
public import Theorems.Thm_Parikh_exists_witness


set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [Finite T] [DecidableEq T] (X : Set (Vector T)) (hX : IsSemilinearSet X) :
    ∃ R : Language T, R.IsRegular ∧ image R = X := by
  classical
  let : Fintype T := Fintype.ofFinite T
  let alphabet : AlphabetOrder T :=
    ⟨Finset.univ.toList, Finset.nodup_toList _, by intro a; simp⟩
  obtain ⟨W, hW⟩ := exists_witness X hX
  obtain ⟨himage, hregular⟩ := witnessExpression_correct alphabet W
  exact ⟨(witnessExpression alphabet W).matches', hregular, himage.trans hW⟩
end Parikh

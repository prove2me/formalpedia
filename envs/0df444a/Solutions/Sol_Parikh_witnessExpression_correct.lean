-- Prove2me | solution 1 for Parikh.witnessExpression_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:55:02.265225+00:00
-- url     : https://prove2.me/submissions/53c61635-7772-4c94-95c4-eaeed86aab59

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Theorems.Thm_Parikh_witnessExpression_image
public import Theorems.Thm_Parikh_witnessExpression_regular

set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [DecidableEq T] (alphabet : AlphabetOrder T) (W : Witness T) :
    image (witnessExpression alphabet W).matches' = W.denotation ∧
      (witnessExpression alphabet W).matches'.IsRegular := by
  exact ⟨witnessExpression_image alphabet W, witnessExpression_regular alphabet W⟩
end Parikh

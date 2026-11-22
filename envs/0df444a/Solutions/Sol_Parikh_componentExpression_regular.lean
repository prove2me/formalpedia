-- Prove2me | solution 1 for Parikh.componentExpression_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:53:23.023963+00:00
-- url     : https://prove2.me/submissions/10c88eab-d889-4cb0-9b4b-ef6cbd47ca03

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Theorems.Thm_Parikh_wordExpression_matches
public import Theorems.Thm_Parikh_periodExpressions_regular
public import Theorems.Thm_Parikh_isRegular_word_mul


set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution (alphabet : AlphabetOrder T) (c : Component T) :
    (componentExpression alphabet c).matches'.IsRegular := by
  change ((wordExpression (representative alphabet c.base)).matches' *
    (c.periods.foldr (fun p (rest : RegularExpression T) =>
      .comp (.star (wordExpression (representative alphabet p))) rest) .epsilon).matches').IsRegular
  rw [wordExpression_matches]
  exact isRegular_word_mul _ _ (periodExpressions_regular alphabet c.periods)
end Parikh

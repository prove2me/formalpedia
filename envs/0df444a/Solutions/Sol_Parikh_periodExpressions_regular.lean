-- Prove2me | solution 1 for Parikh.periodExpressions_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:36.227427+00:00
-- url     : https://prove2.me/submissions/3a3d2642-589f-45d9-af72-98eb3e35b44d

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Theorems.Thm_Parikh_wordExpression_matches
public import Theorems.Thm_Parikh_isRegular_one
public import Theorems.Thm_Parikh_isRegular_word_star_mul


set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution (alphabet : AlphabetOrder T) (periods : List (Vector T)) :
    (periods.foldr (fun p (rest : RegularExpression T) =>
      .comp (.star (wordExpression (representative alphabet p))) rest)
        .epsilon).matches'.IsRegular := by
  induction periods with
  | nil => exact isRegular_one
  | cons p ps ih =>
    change ((wordExpression (representative alphabet p)).star.matches' *
      (ps.foldr (fun q (rest : RegularExpression T) =>
        .comp (.star (wordExpression (representative alphabet q))) rest)
          .epsilon).matches').IsRegular
    rw [RegularExpression.matches'_star, wordExpression_matches]
    exact isRegular_word_star_mul _ _ ih
end Parikh

-- Prove2me | solution 1 for Parikh.witnessExpression_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:54:09.04728+00:00
-- url     : https://prove2.me/submissions/cb5a99e6-bbd0-410c-b9b5-37744f90d128

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Theorems.Thm_Parikh_componentExpression_regular
public import Theorems.Thm_Parikh_isRegular_zero


set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution (alphabet : AlphabetOrder T) (W : Witness T) :
    (witnessExpression alphabet W).matches'.IsRegular := by
  induction W with
  | nil => exact isRegular_zero
  | cons c W ih =>
    exact (componentExpression_regular alphabet c).add ih
end Parikh

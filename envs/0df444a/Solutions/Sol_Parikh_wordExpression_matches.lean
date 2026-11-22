-- Prove2me | solution 1 for Parikh.wordExpression_matches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:00.8368+00:00
-- url     : https://prove2.me/submissions/b43f425f-a484-4712-b816-c486a96e376f

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
theorem _root_.solution (w : List T) :
    (wordExpression w).matches' = {w} := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change ({[a]} : Language T) * (wordExpression w).matches' = {a :: w}
    rw [ih]
    change Set.image2 (fun u z : List T => u ++ z) {[a]} {w} = {a :: w}
    exact Set.image2_singleton
end Parikh

-- Prove2me | solution 1 for Parikh.treeRepresentation_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:54:27.848525+00:00
-- url     : https://prove2.me/submissions/e2014566-4690-49f8-a23f-5fe8c4e0ecb0

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Theorems.Thm_Parikh_treeRepresentation_correct


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    treeRepresentation g = image g.language := by
  exact (treeRepresentation_correct g).1
end Parikh

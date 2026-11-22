-- Prove2me | solution 1 for Parikh.grammar_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:54:25.758816+00:00
-- url     : https://prove2.me/submissions/75ed7d60-c33d-4a93-835b-148beab70ac0

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
    IsSemilinearSet (image g.language) := by
  exact (treeRepresentation_correct g).2
end Parikh

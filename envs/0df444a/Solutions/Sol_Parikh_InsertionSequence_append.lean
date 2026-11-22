-- Prove2me | solution 1 for Parikh.InsertionSequence.append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:32.696217+00:00
-- url     : https://prove2.me/submissions/13a66b83-14cc-4bb9-90e0-d9c1117b886a

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Definitions.Def_LeanPool_Parikh_TreePlugging
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Decomposition

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
namespace InsertionSequence
theorem _root_.solution {g : ContextFreeGrammar T}
    {B middle t : ParseTree T g.NT} {Cs Ds : List (ParseTree T g.NT)}
    (first : InsertionSequence g B Cs middle)
    (second : InsertionSequence g middle Ds t) :
    InsertionSequence g B (Cs ++ Ds) t := by
  induction first with
  | nil _ => simpa only [List.nil_append] using second
  | cons step _ ih => exact .cons step (ih second)
end InsertionSequence
end Parikh

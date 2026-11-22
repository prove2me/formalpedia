-- Prove2me | solution 1 for Parikh.Cycle.root_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:36.232661+00:00
-- url     : https://prove2.me/submissions/b5addc9d-6292-431f-a58a-d373b80e21cb

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
namespace Cycle
theorem _root_.solution {g : ContextFreeGrammar T} {C : ParseTree T g.NT}
    {A : g.NT} (hC : Cycle g C A) : A ∈ C.support := by
  have hsize := hC.2.2
  cases C with
  | terminal a => simp [ParseTree.productionSize] at hsize
  | hole B => simp [ParseTree.productionSize] at hsize
  | node r cs =>
    have hroot : r.input = A := by simpa only [ParseTree.root, Symbol.nonterminal.injEq]
      using hC.2.1
    simp [ParseTree.support, ParseTree.productionLabels, hroot]
end Cycle
end Parikh

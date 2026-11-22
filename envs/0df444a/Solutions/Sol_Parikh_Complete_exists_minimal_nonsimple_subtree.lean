-- Prove2me | solution 1 for Parikh.Complete.exists_minimal_nonsimple_subtree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:25.800194+00:00
-- url     : https://prove2.me/submissions/d3febee1-9893-44d8-bf4e-86eefc3999e6

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
namespace Parikh
namespace Complete
theorem _root_.solution {g : ContextFreeGrammar T}
    {t : ParseTree T g.NT} (ht : Complete g t) (hs : ¬ t.Simple) :
    ∃ q r cs, t.subtree q = some (.node r cs) ∧ Complete g (.node r cs) ∧
      ¬ (ParseTree.node r cs).Simple ∧ ∀ c ∈ cs, c.Simple := by
  obtain ⟨hv, hh⟩ := ht
  induction hv with
  | terminal a => simp [ParseTree.Simple, ParseTree.labelPaths] at hs
  | hole A => simp [ParseTree.holes] at hh
  | node r cs hr hc roots ih =>
    have hholes : ∀ c ∈ cs, c.holes = [] := by
      simpa only [ParseTree.holes, List.flatten_eq_nil_iff, List.forall_mem_map] using hh
    by_cases hsimple : ∀ c ∈ cs, c.Simple
    · exact ⟨[], r, cs, rfl, ⟨.node r cs hr hc roots, hh⟩, hs, hsimple⟩
    · push Not at hsimple
      obtain ⟨c, hcmem, hcs⟩ := hsimple
      obtain ⟨q, r', cs', hq, ht', hs', hchildren⟩ :=
        ih c hcmem hcs (hholes c hcmem)
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hcmem
      exact ⟨i :: q, r', cs', by simp [ParseTree.subtree, hi, hq], ht', hs', hchildren⟩
end Complete
end Parikh

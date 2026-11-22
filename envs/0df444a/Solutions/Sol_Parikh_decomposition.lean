-- Prove2me | solution 1 for Parikh.decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:53.61022+00:00
-- url     : https://prove2.me/submissions/5226494e-76f0-4d8f-8e45-5d9b124e8917

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Definitions.Def_LeanPool_Parikh_TreePlugging
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Theorems.Thm_Parikh_bounded_cut
public import Theorems.Thm_Parikh_InsertionSequence_append

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution (g : ContextFreeGrammar T) (t : ParseTree T g.NT)
    (ht : Complete g t) :
    ∃ B Cs, Complete g B ∧ B.root = t.root ∧ B.Simple ∧
      (∀ C ∈ Cs, IsBoundedCycle g C) ∧ InsertionSequence g B Cs t := by
  classical
  induction hn : t.productionSize using Nat.strong_induction_on generalizing t with
  | h n ih =>
    by_cases hs : t.Simple
    · exact ⟨t, [], ht, rfl, hs, by simp, .nil t⟩
    · obtain ⟨smaller, C, hsmaller, hroot, hbounded, hstep, hsize⟩ :=
        bounded_cut g t ht hs
      obtain ⟨B, Cs, hB, hBroot, hsimple, hCs, hseq⟩ :=
        ih smaller.productionSize (hsize.trans_eq hn) smaller hsmaller rfl
      refine ⟨B, Cs ++ [C], hB, hBroot.trans hroot, hsimple, ?_, ?_⟩
      · intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · exact hCs D hD
        · exact (List.mem_singleton.mp hD) ▸ hbounded
      · exact hseq.append (.cons hstep (.nil t))
end Parikh

-- Prove2me | solution 1 for Parikh.InsertionSequence.accounting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:50.455802+00:00
-- url     : https://prove2.me/submissions/56c01ce1-5d4e-4940-aeb2-20affd9a28b1

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Theorems.Thm_Parikh_insertion_accounting


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
namespace InsertionSequence
theorem _root_.solution [DecidableEq T] {g : ContextFreeGrammar T}
    {B t : ParseTree T g.NT} {Cs : List (ParseTree T g.NT)}
    (h : InsertionSequence g B Cs t) (hB : Complete g B) :
    Complete g t ∧ t.root = B.root ∧
      t.weight = B.weight + (Cs.map ParseTree.weight).sum ∧
      t.productionSize = B.productionSize + (Cs.map ParseTree.productionSize).sum ∧
      t.support = B.support ∪ ⋃ C ∈ Cs, C.support := by
  induction h with
  | nil B => exact ⟨hB, rfl, by simp, by simp, by simp⟩
  | @cons B C next Cs final step rest ih =>
    have hs := insertion_accounting g B C next step
    obtain ⟨hf, hr, hw, hn, hu⟩ := ih step.2.1
    refine ⟨hf, hr.trans hs.1, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      rw [hw, hs.2.1]
      ac_rfl
    · simp only [List.map_cons, List.sum_cons]
      rw [hn, hs.2.2.1]
      omega
    · rw [hu, hs.2.2.2]
      ext A
      simp only [Set.mem_union, Set.mem_iUnion, List.mem_cons]
      aesop
end InsertionSequence
end Parikh

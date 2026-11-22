-- Prove2me | solution 1 for Parikh.ContextsActivatable.realize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:42.260439+00:00
-- url     : https://prove2.me/submissions/89e73034-e84b-4f8a-bbc2-60911c19dcfe

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Activation
public import Theorems.Thm_Parikh_activationOrder_iff_insertionSequence
public import Theorems.Thm_Parikh_Cycle_root_mem_support
public import Theorems.Thm_Parikh_InsertionSequence_accounting
public import Theorems.Thm_Parikh_insertion_enabled


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
namespace ContextsActivatable
theorem _root_.solution {T : Type*} [DecidableEq T]
    {g : ContextFreeGrammar T} {B : ParseTree T g.NT} {D : Finset (ParseTree T g.NT)}
    (hD : ContextsActivatable g B D) (hB : Complete g B) :
    ∃ order t, order.Nodup ∧ (∀ C, C ∈ order ↔ C ∈ D) ∧
      InsertionSequence g B order t ∧ Complete g t ∧ t.root = B.root ∧
      t.weight = B.weight + ∑ C ∈ D, C.weight ∧
      t.support = B.support ∪ ⋃ C ∈ D, C.support ∧
      ∀ C ∈ D, ∃ t', Inserts g t C t' := by
  classical
  obtain ⟨order, hnd, hmem, roots, hcycles, horder⟩ := hD
  obtain ⟨t, hseq⟩ := (activationOrder_iff_insertionSequence roots B order hB
    (fun C hC => hcycles C ((hmem C).mp hC))).mp horder
  obtain ⟨ht, hroot, hweight, _, hsupport⟩ := hseq.accounting hB
  have hset : order.toFinset = D := by
    ext C
    simpa only [List.mem_toFinset] using hmem C
  have hsum : (order.map ParseTree.weight).sum = ∑ C ∈ D, C.weight := by
    rw [← hset]
    exact (List.sum_toFinset ParseTree.weight hnd).symm
  have hsupportD : t.support = B.support ∪ ⋃ C ∈ D, C.support := by
    simpa only [hmem] using hsupport
  refine ⟨order, t, hnd, hmem, hseq, ht, hroot, ?_, hsupportD, ?_⟩
  · simpa only [hsum] using hweight
  · intro C hC
    apply (insertion_enabled g t C (roots C) ht (hcycles C hC)).mpr
    rw [hsupportD]
    apply Or.inr
    simp only [Set.mem_iUnion]
    exact ⟨C, hC, (hcycles C hC).root_mem_support⟩
end ContextsActivatable
end Parikh

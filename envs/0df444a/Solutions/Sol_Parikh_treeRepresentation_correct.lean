-- Prove2me | solution 1 for Parikh.treeRepresentation_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:53:50.843801+00:00
-- url     : https://prove2.me/submissions/ed47ec24-7a7e-4209-ad87-744336a94799

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_FiniteRepresentation
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Theorems.Thm_Parikh_InsertionSequence_accounting
public import Theorems.Thm_Parikh_InsertionSequence_contextsActivatable
public import Theorems.Thm_Parikh_decomposition
public import Theorems.Thm_Parikh_derives_iff_tree
public import Theorems.Thm_Parikh_one_linear
public import Theorems.Thm_Parikh_treeRepresentation_isSemilinearSet


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    treeRepresentation g = image g.language ∧ IsSemilinearSet (image g.language) := by
  have heq : treeRepresentation g = image g.language := by
    classical
    ext v
    constructor
    · -- Realize a component vector by insertions, then read the resulting word.
      rintro ⟨B, D, hB, _, hD, hv⟩
      rw [← one_linear g B D hB.1 hD] at hv
      obtain ⟨t, Cs, hseq, _, hweight⟩ := hv
      obtain ⟨ht, hroot, _, _, _⟩ := hseq.accounting hB.1
      refine ⟨t.yield, ?_, hweight⟩
      exact (g.mem_language_iff t.yield).mpr
        ((derives_iff_tree g g.initial t.yield).mpr
          ⟨t, ht, hroot.trans hB.2.1, rfl⟩)
    · -- Decompose a word's derivation tree and collect the contexts it uses.
      rintro ⟨w, hw, rfl⟩
      obtain ⟨t, ht, hroot, hyield⟩ :=
        (derives_iff_tree g g.initial w).mp ((g.mem_language_iff w).mp hw)
      obtain ⟨B, Cs, hB, hBroot, hsimple, hbounded, hseq⟩ := decomposition g t ht
      have hD := hseq.contextsActivatable hB
      refine ⟨B, Cs.toFinset, ⟨hB, hBroot.trans hroot, hsimple⟩,
        fun C hC => hbounded C (List.mem_toFinset.mp hC), hD, ?_⟩
      rw [← one_linear g B Cs.toFinset hB hD]
      exact ⟨t, Cs, hseq, fun C => List.mem_toFinset.symm,
        by simp only [ParseTree.weight, hyield]⟩
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact treeRepresentation_isSemilinearSet g
end Parikh

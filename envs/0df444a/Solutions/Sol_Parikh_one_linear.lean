-- Prove2me | solution 1 for Parikh.one_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:53:13.542174+00:00
-- url     : https://prove2.me/submissions/4e81af59-fce6-42ea-a78d-735bbe1e4980

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Activation
public import Theorems.Thm_Parikh_positive_multiplicities
public import Theorems.Thm_Parikh_activationOrder_iff_insertionSequence
public import Theorems.Thm_Parikh_contextComponent_mem_denotation_iff
public import Theorems.Thm_Parikh_Cycle_root_mem_support
public import Theorems.Thm_Parikh_InsertionSequence_accounting


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} [DecidableEq T] (g : ContextFreeGrammar T)
    (B : ParseTree T g.NT) (D : Finset (ParseTree T g.NT))
    (hB : Complete g B) (hD : ContextsActivatable g B D) :
    {v | ∃ t Cs, InsertionSequence g B Cs t ∧
      (∀ C, C ∈ Cs ↔ C ∈ D) ∧ t.weight = v} =
      (contextComponent B D).denotation := by
  classical
  have sum_counts : ∀ (Cs : List (ParseTree T g.NT))
      (hmem : ∀ C, C ∈ Cs ↔ C ∈ D),
      (Cs.map ParseTree.weight).sum = ∑ C ∈ D, Cs.count C • C.weight := by
    intro Cs hmem
    have hset : Cs.toFinset = D := by
      ext C
      simpa only [List.mem_toFinset] using hmem C
    rw [Finset.sum_list_map_count, hset]
  ext v
  rw [contextComponent.mem_denotation_iff]
  constructor
  · rintro ⟨t, Cs, hseq, hmem, rfl⟩
    refine ⟨fun C => Cs.count C - 1, ?_⟩
    rw [(hseq.accounting hB).2.2.1, sum_counts Cs hmem]
    have hsplit : ∑ C ∈ D, Cs.count C • C.weight =
        (∑ C ∈ D, C.weight) + ∑ C ∈ D, (Cs.count C - 1) • C.weight := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro C hC
      have hpositive : 0 < Cs.count C := List.count_pos_iff.mpr ((hmem C).mpr hC)
      have hcount : Cs.count C = 1 + (Cs.count C - 1) := by omega
      conv_lhs => rw [hcount]
      rw [add_nsmul, one_nsmul]
    rw [hsplit, add_assoc]
  · rintro ⟨k, rfl⟩
    obtain ⟨order, hnd, hmem, roots, hcycles, horder⟩ := hD
    have hact : Activatable roots ParseTree.support B.support D := ⟨order, hnd, hmem, horder⟩
    obtain ⟨Cs, hCs, hCs_mem, hcount⟩ := positive_multiplicities roots ParseTree.support
      B.support D (fun C hC => (hcycles C hC).root_mem_support) hact
      (fun C => k C + 1) (by simp)
    obtain ⟨t, hseq⟩ := (activationOrder_iff_insertionSequence roots B Cs hB
      (fun C hC => hcycles C ((hCs_mem C).mp hC))).mp hCs
    refine ⟨t, Cs, hseq, hCs_mem, ?_⟩
    rw [(hseq.accounting hB).2.2.1, sum_counts Cs hCs_mem]
    have hsplit : ∑ C ∈ D, Cs.count C • C.weight =
        (∑ C ∈ D, C.weight) + ∑ C ∈ D, k C • C.weight := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro C hC
      rw [hcount C hC, add_nsmul, one_nsmul, add_comm]
    rw [hsplit, add_assoc]
end Parikh

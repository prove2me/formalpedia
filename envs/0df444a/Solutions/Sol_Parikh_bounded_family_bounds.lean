-- Prove2me | solution 1 for Parikh.bounded_family_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:35.086454+00:00
-- url     : https://prove2.me/submissions/73d5e606-8855-4e03-b403-b3be0c36f04f

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Data.Nat.Log
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Parikh_Construction
public import Theorems.Thm_Parikh_ParseTree_norm_weight_eq_length
public import Theorems.Thm_Parikh_Cycle_root_mem_support
public import Theorems.Thm_Parikh_Valid_support_active
public import Theorems.Thm_Parikh_card_treeFamily_le
public import Theorems.Thm_Parikh_mem_treeFamily
public import Theorems.Thm_Parikh_simple_height
public import Theorems.Thm_Parikh_yield_length_le_heightPositions


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} [Fintype T] [DecidableEq T]
    (g : ContextFreeGrammar T) :
    (∃ bases : Finset (ParseTree T g.NT),
      (∀ B, B ∈ bases ↔ IsBase g B) ∧ bases.card ≤ (grammarSize g).trees) ∧
    (∃ cycles : Finset (ParseTree T g.NT),
      (∀ C, C ∈ cycles ↔ IsBoundedCycle g C) ∧ cycles.card ≤ (grammarSize g).trees) ∧
    (∀ t, IsBase g t ∨ IsBoundedCycle g t → norm t.weight ≤ (grammarSize g).positions) := by
  classical
  let s := grammarSize g
  have hb : ∀ r ∈ g.rules, r.output.length ≤ s.branching := by
    intro r hr
    exact (Finset.le_sup (f := fun r => r.output.length) hr).trans (Nat.le_max_right _ _)
  have hbounded : ∀ t, IsBase g t ∨ IsBoundedCycle g t →
      ActiveOpen g t ∧ t.height ≤ s.nonterminals + 1 := by
    intro t ht
    rcases ht with hbase | hcycle
    · refine ⟨⟨hbase.1.1, ?_⟩, ?_⟩
      · simp [hbase.1.2]
      · exact (simple_height g t hbase.1 hbase.2.2).trans (Nat.le_succ _)
    · obtain ⟨⟨A, hcycle⟩, hh⟩ := hcycle
      refine ⟨⟨hcycle.1.1, ?_⟩, hh⟩
      intro B hB
      have hBA : B = A := by simpa only [hcycle.1.2, List.mem_singleton] using hB
      subst B
      exact hcycle.1.1.support_active hcycle.root_mem_support
  let family := treeFamily g (s.nonterminals + 1)
  have hmem : ∀ t, IsBase g t ∨ IsBoundedCycle g t → t ∈ family := by
    intro t ht
    obtain ⟨ho, hh⟩ := hbounded t ht
    exact mem_treeFamily g _ t ho hh
  have hcard : family.card ≤ s.trees := by
    exact card_treeFamily_le g s.branching s.records (by rfl) hb _
  refine ⟨⟨family.filter (IsBase g), ?_, ?_⟩,
    ⟨family.filter (IsBoundedCycle g), ?_, ?_⟩, ?_⟩
  · intro B
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨hmem B (Or.inl h), h⟩⟩
  · exact (Finset.card_filter_le _ _).trans hcard
  · intro C
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨hmem C (Or.inr h), h⟩⟩
  · exact (Finset.card_filter_le _ _).trans hcard
  · intro t ht
    obtain ⟨ho, hh⟩ := hbounded t ht
    rw [ParseTree.norm_weight_eq_length]
    exact yield_length_le_heightPositions g s.branching hb _ t ho.1 hh
end Parikh

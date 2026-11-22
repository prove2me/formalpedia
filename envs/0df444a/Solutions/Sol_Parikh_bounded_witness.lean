-- Prove2me | solution 1 for Parikh.bounded_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:55:01.808142+00:00
-- url     : https://prove2.me/submissions/221a6d70-f4bd-48be-92e9-472b06989482

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Data.Nat.Log
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Parikh_Construction
public import Theorems.Thm_Parikh_bounded_family_bounds
public import Theorems.Thm_Parikh_contextComponent_size_bounds
public import Theorems.Thm_Parikh_familyWitness_denotation
public import Theorems.Thm_Parikh_familyWitness_length_le
public import Theorems.Thm_Parikh_mem_familyWitness


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} [Fintype T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ W : Witness T, W.denotation = image g.language ∧ WithinBounds (grammarSize g) W := by
  classical
  obtain ⟨⟨bases, hb, hbcard⟩, ⟨cycles, hc, hccard⟩, hnorm⟩ := bounded_family_bounds g
  refine ⟨familyWitness g bases cycles, familyWitness_denotation g bases cycles hb hc, ?_⟩
  refine ⟨(familyWitness_length_le g bases cycles).trans ?_, ?_⟩
  · exact Nat.mul_le_mul hbcard (Nat.pow_le_pow_right (by omega) hccard)
  · intro c hmem
    obtain ⟨B, hB, D, hD, _, rfl⟩ := (mem_familyWitness g bases cycles c).mp hmem
    have hDcard : D.card ≤ (grammarSize g).trees := (Finset.card_le_card hD).trans hccard
    obtain ⟨hlen, hbase, hperiod⟩ := contextComponent_size_bounds B D (grammarSize g).positions
      (hnorm B (Or.inl ((hb B).mp hB)))
      (fun C hC => hnorm C (Or.inr ((hc C).mp (hD hC))))
    exact ⟨hlen.le.trans hDcard,
      hbase.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hDcard 1)), hperiod⟩
end Parikh

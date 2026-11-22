-- Prove2me | solution 1 for Parikh.familyWitness_denotation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:54:26.304802+00:00
-- url     : https://prove2.me/submissions/443baf84-12a0-419c-8b02-1a5ed6ce4ce1

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
public import Theorems.Thm_Parikh_mem_familyWitness
public import Theorems.Thm_Parikh_treeRepresentation_correct


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} [DecidableEq T]
namespace Parikh
theorem _root_.solution [Finite T] (g : ContextFreeGrammar T)
    (bases cycles : Finset (ParseTree T g.NT))
    (hb : ∀ B, B ∈ bases ↔ IsBase g B)
    (hc : ∀ C, C ∈ cycles ↔ IsBoundedCycle g C) :
    (familyWitness g bases cycles).denotation = image g.language := by
  classical
  rw [← (treeRepresentation_correct g).1]
  ext v
  constructor
  · rintro ⟨c, hmem, hv⟩
    obtain ⟨B, hB, D, hD, ha, rfl⟩ := (mem_familyWitness g bases cycles c).mp hmem
    exact ⟨B, D, (hb B).mp hB, fun C hC => (hc C).mp (hD hC), ha, hv⟩
  · rintro ⟨B, D, hB, hD, ha, hv⟩
    refine ⟨contextComponent B D, ?_, hv⟩
    exact (mem_familyWitness g bases cycles _).mpr
      ⟨B, (hb B).mpr hB, D, fun C hC => (hc C).mpr (hD C hC), ha, rfl⟩
end Parikh

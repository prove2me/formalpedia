-- Prove2me | solution 1 for Parikh.mem_familyWitness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:20.881805+00:00
-- url     : https://prove2.me/submissions/51a10410-81f3-4332-a6f7-b0b876d55eb7

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_FiniteWitness

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} [DecidableEq T]
namespace Parikh
theorem _root_.solution (g : ContextFreeGrammar T)
    (bases cycles : Finset (ParseTree T g.NT)) (c : Component T) :
    c ∈ familyWitness g bases cycles ↔
      ∃ B ∈ bases, ∃ D : Finset (ParseTree T g.NT),
        D ⊆ cycles ∧ ContextsActivatable g B D ∧ contextComponent B D = c := by
  classical
  simp only [familyWitness, List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_product, Finset.mem_powerset, Prod.exists]
  constructor
  · rintro ⟨B, D, ⟨⟨hB, hD⟩, ha⟩, hc⟩
    exact ⟨B, hB, D, hD, ha, hc⟩
  · rintro ⟨B, hB, D, hD, ha, hc⟩
    exact ⟨B, D, ⟨⟨hB, hD⟩, ha⟩, hc⟩
end Parikh

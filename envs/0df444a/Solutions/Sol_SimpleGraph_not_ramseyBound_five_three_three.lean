-- Prove2me | solution 1 for SimpleGraph.not_ramseyBound_five_three_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:38.651299+00:00
-- url     : https://prove2.me/submissions/d2a8a625-9017-4298-acd2-8eff43e8c5b6

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
namespace SimpleGraph
theorem _root_.solution : ¬RamseyBound 5 3 3 := by
  intro h
  have hfree : (cycleGraph 5).CliqueFree 3 ∧ (cycleGraph 5)ᶜ.CliqueFree 3 := by
    constructor <;>
    · intro t ht
      rw [is3Clique_iff] at ht
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
      revert a b c
      decide
  rcases h (cycleGraph 5) with ⟨t, ht⟩ | ⟨t, ht⟩
  exacts [hfree.1 t ht, hfree.2 t ht]
end SimpleGraph

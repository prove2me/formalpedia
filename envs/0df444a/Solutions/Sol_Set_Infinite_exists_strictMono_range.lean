-- Prove2me | solution 1 for Set.Infinite.exists_strictMono_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:01.048218+00:00
-- url     : https://prove2.me/submissions/36b27da9-f74f-41f8-9059-9ed798c19c4a

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Data.Nat.Nth
public import Definitions.Def_LeanPool_NashWilliams_Data_Nat_Nth

set_option autoImplicit true
@[expose] public section
public section
namespace Set.Infinite
theorem _root_.solution {X : Set ℕ} (hX : X.Infinite) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ Set.range N = X := by
  have hp : (Set.ofPred fun n => n ∈ X).Infinite := by
    simpa only [Set.ofPred_mem_eq] using hX
  refine ⟨Nat.nth (· ∈ X), Nat.nth_strictMono hp, ?_⟩
  simpa only [Set.ofPred_mem_eq] using Nat.range_nth_of_infinite hp
end Set.Infinite

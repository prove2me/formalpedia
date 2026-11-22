-- Prove2me | solution 1 for Set.Infinite.exists_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:27.5222+00:00
-- url     : https://prove2.me/submissions/36d8dca6-893a-4eba-be44-f3914e1ff9a2

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Data.Nat.Nth
public import Definitions.Def_LeanPool_NashWilliams_Data_Nat_Nth
public import Theorems.Thm_Set_Infinite_exists_strictMono_range

set_option autoImplicit true
@[expose] public section
public section
namespace Set.Infinite
theorem _root_.solution {s : Set ℕ} (hs : s.Infinite) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, e i ∈ s := by
  obtain ⟨N, hN, hrange⟩ := hs.exists_strictMono_range
  exact ⟨N, hN, fun i => hrange ▸ Set.mem_range_self i⟩
end Set.Infinite

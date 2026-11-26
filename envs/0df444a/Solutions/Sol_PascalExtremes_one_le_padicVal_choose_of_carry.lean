-- Prove2me | solution 1 for PascalExtremes.one_le_padicVal_choose_of_carry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:56:09.768028+00:00
-- url     : https://prove2.me/submissions/fcb26a47-a3f7-4f3f-82d6-2359d9f42601

module
public import Definitions.Def_PascalExtremes_Kummer
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic
public import Definitions.Def_PascalExtremes_CarryBounds
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
public import Theorems.Thm_PascalExtremes_padicVal_choose_eq_carryCount
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff



set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p n k i : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hi : 1 ≤ i)
    (hcarry : CarryAt p n k i) :
    1 ≤ padicValNat p (n.choose k) := by
  letI : Fact p.Prime := ⟨hp⟩
  let b := max (Nat.log p n + 1) (i + 1)
  have hnb : Nat.log p n < b := by
    dsimp [b]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  rw [padicVal_choose_eq_carryCount hkn hnb, carryCount]
  apply Finset.card_pos.mpr
  refine ⟨i, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨hi, ?_⟩, hcarry⟩
  dsimp [b]
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
end PascalExtremes

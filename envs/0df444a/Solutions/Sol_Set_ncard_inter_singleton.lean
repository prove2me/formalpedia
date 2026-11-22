-- Prove2me | solution 1 for Set.ncard_inter_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:30:42.380674+00:00
-- url     : https://prove2.me/submissions/5b8a0be5-85df-4630-a8fe-c4e4fb9a53db

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Card

set_option autoImplicit true
@[expose] public section
public section
open Set
variable {α : Type*}
namespace Set
theorem _root_.solution (a : α) (s : Set α) [Decidable (a ∈ s)] :
    (s ∩ {a}).ncard = if a ∈ s then 1 else 0 := by
  split_ifs <;> simp [*]
end Set

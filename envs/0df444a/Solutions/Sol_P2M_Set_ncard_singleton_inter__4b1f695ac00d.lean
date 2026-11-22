-- Prove2me | solution 1 for P2M_Set_ncard_singleton_inter__4b1f695ac00d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:45:53.353424+00:00
-- url     : https://prove2.me/submissions/d36ad43a-522f-49c1-9402-511e0db8c6c3

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
    ({a} ∩ s).ncard = if a ∈ s then 1 else 0 := by
  split_ifs <;> simp [*]
end Set

-- Prove2me | solution 1 for TunnellMap.insertB_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:30.580373+00:00
-- url     : https://prove2.me/submissions/8bed1c14-8236-44ee-a992-68cd5aac80fb

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
import Theorems.Thm_TunnellMap_isqrtK_eq
attribute [local simp] TunnellMap.isqrtK_eq

set_option autoImplicit true
open TunnellMap
variable {α : Type*}
namespace TunnellMap
theorem _root_.solution (le : α → α → Bool) (a : α) (l : List α) :
    (insertB le a l).Perm (a :: l) := by
  induction l with
  | nil => simp [insertB]
  | cons b l ih =>
      by_cases h : le a b
      · simp [insertB, h]
      · simp only [insertB, h, Bool.false_eq_true, if_false]
        exact ((ih.cons b).trans (List.Perm.swap a b l))
end TunnellMap

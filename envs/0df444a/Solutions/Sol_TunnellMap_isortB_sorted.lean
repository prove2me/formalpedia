-- Prove2me | solution 1 for TunnellMap.isortB_sorted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:37.510652+00:00
-- url     : https://prove2.me/submissions/66b41113-2193-4faf-a779-76691ef2b0c6

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
import Theorems.Thm_TunnellMap_isqrtK_eq
import Theorems.Thm_TunnellMap_insertB_sorted
attribute [local simp] TunnellMap.isqrtK_eq

set_option autoImplicit true
open TunnellMap
variable {α : Type*}
namespace TunnellMap
theorem _root_.solution (le : α → α → Bool)
    (htotal : ∀ a b, le a b = true ∨ le b a = true)
    (htrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (l : List α) : (isortB le l).Pairwise fun x y => le x y = true := by
  induction l with
  | nil => simp [isortB]
  | cons a l ih => exact insertB_sorted le htotal htrans a ih
end TunnellMap

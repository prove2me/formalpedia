-- Prove2me | solution 1 for TunnellMap.isortB_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:27.702899+00:00
-- url     : https://prove2.me/submissions/985a9ee4-94bf-420d-8a0c-92df5903b520

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
import Theorems.Thm_TunnellMap_isqrtK_eq
import Theorems.Thm_TunnellMap_insertB_perm
attribute [local simp] TunnellMap.isqrtK_eq

set_option autoImplicit true
open TunnellMap
variable {α : Type*}
namespace TunnellMap
theorem _root_.solution (le : α → α → Bool) (l : List α) : (isortB le l).Perm l := by
  induction l with
  | nil => simp [isortB]
  | cons a l ih => exact (insertB_perm le a (isortB le l)).trans (ih.cons a)
end TunnellMap

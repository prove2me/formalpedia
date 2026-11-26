-- Prove2me | solution 1 for TunnellMap.mergeSort_eq_isortB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:52:45.982864+00:00
-- url     : https://prove2.me/submissions/0a8918c3-4a34-4299-a1af-f956af274247

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
import Theorems.Thm_TunnellMap_isqrtK_eq
import Theorems.Thm_TunnellMap_isortB_perm
import Theorems.Thm_TunnellMap_isortB_sorted
attribute [local simp] TunnellMap.isqrtK_eq

set_option autoImplicit true
open TunnellMap
variable {α : Type*}
namespace TunnellMap
theorem _root_.solution (le : α → α → Bool)
    (htotal : ∀ a b, le a b = true ∨ le b a = true)
    (htrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    {l : List α}
    (hanti : ∀ a ∈ l, ∀ b ∈ l, le a b = true → le b a = true → a = b) :
    l.mergeSort le = isortB le l := by
  have hperm₁ : (l.mergeSort le).Perm l := List.mergeSort_perm _ _
  have hperm₂ : (isortB le l).Perm l := isortB_perm le l
  refine List.Perm.eq_of_pairwise (le := fun x y => le x y = true) ?_ ?_ ?_
    (hperm₁.trans hperm₂.symm)
  · intro a b ha hb hab hba
    exact hanti a (hperm₁.mem_iff.mp ha) b (hperm₂.mem_iff.mp hb) hab hba
  · exact List.pairwise_mergeSort (fun {a b c} => htrans a b c)
      (fun a b => by simpa using htotal a b) l
  · exact isortB_sorted le htotal htrans l
end TunnellMap

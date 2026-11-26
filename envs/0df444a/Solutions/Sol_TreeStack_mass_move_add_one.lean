-- Prove2me | solution 1 for TreeStack.mass_move_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:54.740799+00:00
-- url     : https://prove2.me/submissions/031675bd-9326-4e3b-af00-ffb718db7586

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff



set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V]
    (C : Configuration V) {u v : V} (huv : u ≠ v) (hu : 2 ≤ C u) :
    mass (move C u v) + 1 = mass C := by
  classical
  simp only [mass, move]
  rw [Finset.sum_update_of_mem (Finset.mem_univ v),
    Finset.sdiff_singleton_eq_erase]
  have huv_mem : u ∈ Finset.univ.erase v := by simp [huv]
  rw [Finset.sum_update_of_mem (s := Finset.univ.erase v) (i := u)
      (f := C) (b := C u - 2) huv_mem,
    Finset.sdiff_singleton_eq_erase]
  have hv := Finset.sum_erase_add Finset.univ C (Finset.mem_univ v)
  have hu' := Finset.sum_erase_add (Finset.univ.erase v) C huv_mem
  omega
end TreeStack

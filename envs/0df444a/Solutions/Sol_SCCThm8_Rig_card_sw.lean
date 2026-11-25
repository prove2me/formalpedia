-- Prove2me | solution 1 for SCCThm8.Rig.card_sw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:47:39.802779+00:00
-- url     : https://prove2.me/submissions/7ac6d89d-9a23-4e37-8b46-7e3833a8727c

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
namespace SCCThm8.Rig
theorem _root_.solution {A : Finset (Fin n)} {k : ℕ} {i j : Fin n} (hA : A.card = k) (hi : i ∈ A)
    (hj : j ∉ A) : (sw A i j).card = k := by
  have h1 : j ∉ A.erase i := fun h => hj (mem_of_mem_erase h)
  rw [sw, card_insert_of_notMem h1, card_erase_of_mem hi]
  have := card_pos.mpr ⟨i, hi⟩
  omega
end SCCThm8.Rig

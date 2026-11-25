-- Prove2me | solution 1 for SCCThm8.Rig.sw_sw_back
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:59.418828+00:00
-- url     : https://prove2.me/submissions/0faf559d-2d40-44c9-aa6e-ef2aa362f080

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_mem_sw

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
namespace SCCThm8.Rig
theorem _root_.solution {A : Finset (Fin n)} {i j : Fin n} (hi : i ∈ A) (hj : j ∉ A) :
    sw (sw A i j) j i = A := by
  ext x; simp only [mem_sw]; grind
end SCCThm8.Rig

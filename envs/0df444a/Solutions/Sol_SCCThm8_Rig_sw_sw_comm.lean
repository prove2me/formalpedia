-- Prove2me | solution 1 for SCCThm8.Rig.sw_sw_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:08.539973+00:00
-- url     : https://prove2.me/submissions/35ee1d58-55ae-4528-9316-66f7c2d1cceb

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
theorem _root_.solution {A : Finset (Fin n)} {i i' j j' : Fin n} (h1 : i' ≠ j) (h2 : i' ≠ j') :
    sw (sw A i j) i' j' = sw (sw A i j') i' j := by
  ext x; simp only [mem_sw]; grind
end SCCThm8.Rig

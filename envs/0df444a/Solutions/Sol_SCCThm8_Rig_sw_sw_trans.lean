-- Prove2me | solution 1 for SCCThm8.Rig.sw_sw_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:02.368884+00:00
-- url     : https://prove2.me/submissions/9109feae-9a87-421f-b1a2-58b9d76bee0e

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
theorem _root_.solution {A : Finset (Fin n)} {i j l : Fin n} (hj : j ∉ A) :
    sw (sw A i j) j l = sw A i l := by
  ext x; simp only [mem_sw]; grind
end SCCThm8.Rig

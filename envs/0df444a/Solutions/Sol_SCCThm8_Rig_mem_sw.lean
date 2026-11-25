-- Prove2me | solution 1 for SCCThm8.Rig.mem_sw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:47:37.433029+00:00
-- url     : https://prove2.me/submissions/c39779e0-615b-470e-90fd-b6198ac7d8ec

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
theorem _root_.solution {A : Finset (Fin n)} {i j x : Fin n} : x ∈ sw A i j ↔ x = j ∨ (x ≠ i ∧ x ∈ A) := by
  simp [sw, mem_insert, mem_erase]
end SCCThm8.Rig

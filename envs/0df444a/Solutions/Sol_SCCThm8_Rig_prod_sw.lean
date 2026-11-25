-- Prove2me | solution 1 for SCCThm8.Rig.prod_sw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:12.37366+00:00
-- url     : https://prove2.me/submissions/a8a53b68-ee77-42a6-9c65-120d2347d863

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
theorem _root_.solution {H : Type*} [CommGroup H] (g' : Fin n → H) {A : Finset (Fin n)} {i j : Fin n}
    (hi : i ∈ A) (hj : j ∉ A) :
    ∏ x ∈ sw A i j, g' x = g' j * (g' i)⁻¹ * ∏ x ∈ A, g' x := by
  have h1 : j ∉ A.erase i := fun h => hj (mem_of_mem_erase h)
  rw [sw, prod_insert h1, ← mul_prod_erase A g' hi]
  group
end SCCThm8.Rig

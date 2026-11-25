-- Prove2me | solution 1 for SCCThm8.Rig.comm_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:31.975424+00:00
-- url     : https://prove2.me/submissions/d38a0557-7b50-4272-b811-503232f89306

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
theorem _root_.solution {H : Type*} [CommGroup H] (a b c d e : H) :
    a * b⁻¹ * c⁻¹ * d = a * e * d * (b * e * c)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end SCCThm8.Rig

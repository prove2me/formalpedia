-- Prove2me | solution 1 for QuadraticFloor.sum_quadraticChar_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:44:51.184827+00:00
-- url     : https://prove2.me/submissions/705e8ecf-6928-449d-8b58-bc26766c1615

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) (b : ZMod p) :
    ∑ y : ZMod p, quadraticChar (ZMod p) (b + a * y) = 0 := by
  have hch : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  let e : ZMod p ≃ ZMod p :=
    { toFun := fun y => b + a * y
      invFun := fun z => (z - b) * a⁻¹
      left_inv := fun y => by simp only; field_simp; ring
      right_inv := fun z => by simp only; field_simp; ring }
  rw [show (∑ y : ZMod p, quadraticChar (ZMod p) (b + a * y)) =
      ∑ y : ZMod p, quadraticChar (ZMod p) (e y) from rfl, Equiv.sum_comp e,
      quadraticChar_sum_zero hch]
end QuadraticFloor

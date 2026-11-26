-- Prove2me | solution 1 for QuadraticFloor.negOnePow_emod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:03.538354+00:00
-- url     : https://prove2.me/submissions/19d30441-985d-45e5-9a0c-050ce04f6e88

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
theorem _root_.solution (v : ℤ) :
    ((v % (p : ℤ)).negOnePow : ℤ) = (-1) ^ ((v : ZMod p).val) := by
  rw [← ZMod.val_intCast v, Int.coe_negOnePow_natCast]
end QuadraticFloor

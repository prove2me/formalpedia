-- Prove2me | solution 1 for QuadraticFloor.zmod3_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:58.796306+00:00
-- url     : https://prove2.me/submissions/1e37f767-86ec-46ec-8659-7fb20a67a25f

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
end QuadraticFloor

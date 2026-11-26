-- Prove2me | solution 1 for QuadraticFloor.chi3_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:50:57.893747+00:00
-- url     : https://prove2.me/submissions/e4a6678c-3a10-4ffb-a82e-10d1437626bb

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
theorem _root_.solution (x : ℕ) : chi3 (x : ZMod 3) = (legendreSym 3 x : ℂ) := by
  simp [chi3, legendreSym]
end QuadraticFloor

-- Prove2me | solution 1 for QuadraticFloor.eta_of_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:44:30.637799+00:00
-- url     : https://prove2.me/submissions/666d7322-1c3e-42fb-b1bf-975725d49f17

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace QuadraticFloor
theorem _root_.solution {x : ℕ} (hx : Even x) : eta p x = 0 := by simp [eta, hx]
end QuadraticFloor

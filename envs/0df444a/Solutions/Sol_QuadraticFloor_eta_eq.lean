-- Prove2me | solution 1 for QuadraticFloor.eta_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:28.279585+00:00
-- url     : https://prove2.me/submissions/6a8d5733-1b84-4217-8c72-852b4a1962b2

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_eta_eq__74b5fa8b45c2


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (x : ℕ) : eta p x = kap p x * legendreSym p x :=
  eta_eq' hp2 x
end QuadraticFloor

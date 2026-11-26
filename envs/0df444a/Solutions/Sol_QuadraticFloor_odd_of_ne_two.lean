-- Prove2me | solution 1 for QuadraticFloor.odd_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:36.730782+00:00
-- url     : https://prove2.me/submissions/cd17019e-c672-4c18-9322-87baec4e91b1

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
theorem _root_.solution (hp2 : p ≠ 2) : Odd p := hp.out.odd_of_ne_two hp2
end QuadraticFloor

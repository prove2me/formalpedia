-- Prove2me | solution 1 for QuadraticFloor.admissible_five_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:23.282287+00:00
-- url     : https://prove2.me/submissions/a2f17a5e-724f-4029-bc55-62dabf3136ab

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution : Admissible 5 3 0 := ⟨by decide, by decide, by norm_num, by norm_num⟩
end QuadraticFloor

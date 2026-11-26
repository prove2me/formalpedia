-- Prove2me | solution 1 for QuadraticFloor.admissible_five_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:12.791476+00:00
-- url     : https://prove2.me/submissions/b50a4e8c-ce73-4817-93fd-6820d290ee41

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
theorem _root_.solution : Admissible 5 1 0 := ⟨odd_one, by decide, by norm_num, by norm_num⟩
end QuadraticFloor

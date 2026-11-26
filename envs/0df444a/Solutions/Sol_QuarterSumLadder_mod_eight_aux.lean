-- Prove2me | solution 1 for QuarterSumLadder.mod_eight_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:00:42.960844+00:00
-- url     : https://prove2.me/submissions/fe567a34-b95a-45a1-881b-edf21be4d4ee

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace QuarterSumLadder
theorem _root_.solution (hp8 : p % 8 = 1) : p - 1 = 4 * Q p := by unfold Q; omega
end QuarterSumLadder

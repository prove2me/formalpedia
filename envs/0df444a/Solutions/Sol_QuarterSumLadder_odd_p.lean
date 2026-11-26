-- Prove2me | solution 1 for QuarterSumLadder.odd_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:55:57.345857+00:00
-- url     : https://prove2.me/submissions/645c6402-dab2-40e0-9c37-728a592e4131

module
public import Definitions.Def_QuarterSumLadder_Defs
public import Definitions.Def_QuarterSumLadder_Prelim

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution (hp2 : p ≠ 2) : Odd p := hp.out.odd_of_ne_two hp2
end QuarterSumLadder

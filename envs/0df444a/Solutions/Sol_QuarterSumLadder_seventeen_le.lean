-- Prove2me | solution 1 for QuarterSumLadder.seventeen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:44.262795+00:00
-- url     : https://prove2.me/submissions/eedf93d0-678b-44b7-9522-0b767e4e6892

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution (hp8 : p % 8 = 1) : 17 ≤ p := by
  by_contra h
  have h2 := hp.out.two_le
  have : p = 9 := by omega
  subst this; exact absurd hp.out (by norm_num)
end QuarterSumLadder

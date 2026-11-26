-- Prove2me | solution 1 for QuarterSumLadder.hp2_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:59:42.418382+00:00
-- url     : https://prove2.me/submissions/e175a9fa-0719-4f62-ab62-8fe9f959894e

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
theorem _root_.solution (hp8 : p % 8 = 1) : p ≠ 2 := by omega
end QuarterSumLadder

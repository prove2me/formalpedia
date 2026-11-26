-- Prove2me | solution 1 for QuarterSumLadder.gi_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:06:44.290879+00:00
-- url     : https://prove2.me/submissions/3875348d-2519-4659-a372-5ae087413ace

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_gi_sq


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution : gi ^ 3 = -gi := by rw [pow_succ, gi_sq]; ring
end QuarterSumLadder

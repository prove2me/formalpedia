-- Prove2me | solution 1 for QuarterSumLadder.ne_zero_of_mem_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:01:05.311408+00:00
-- url     : https://prove2.me/submissions/b9223e73-bedf-40fc-a45b-078604dbdd59

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_mem_fiber

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution {x : ZMod p} {z : GaussianInt} (hz : z ≠ 0) (hx : x ∈ fiber χ z) :
    x ≠ 0 := by
  rintro rfl; rw [mem_fiber, MulChar.map_zero] at hx; exact hz hx.symm
end QuarterSumLadder

-- Prove2me | solution 1 for QuarterSumLadder.half_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:05:39.736908+00:00
-- url     : https://prove2.me/submissions/6fdf776d-7f56-4f9e-b189-20604276a4ec

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution {x : ZMod p} (h : 4 * x.val < p) : 2 * x.val < p := by omega
end QuarterSumLadder

-- Prove2me | solution 1 for QuarterSumLadder.neg_mem_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:04:13.520342+00:00
-- url     : https://prove2.me/submissions/241aa463-d799-42cb-b34e-b875a956dfa3

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_mem_fiber
public import Theorems.Thm_QuarterSumLadder_char_neg

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution {x : ZMod p} {z : GaussianInt} (h : x ∈ fiber χ z) : -x ∈ fiber χ z := by
  rw [mem_fiber] at *; rw [char_neg hp8 hχ, h]
end QuarterSumLadder
